#!/usr/bin/env python3
from __future__ import annotations

import argparse
import dataclasses
import pathlib
import sys
from typing import Iterable


def _require_pyarrow() -> tuple[object, object, object]:
    try:
        import pyarrow as pa  # noqa: F401
        import pyarrow.compute as pc  # noqa: F401
        import pyarrow.parquet as pq  # noqa: F401
    except Exception as exc:
        msg = (
            "error: pyarrow is required to read parquet.\n"
            "Install in a venv, e.g.:\n"
            "  apt-get install -y python3-venv\n"
            "  python3 -m venv external/pyvenv\n"
            "  external/pyvenv/bin/pip install pyarrow\n"
        )
        raise RuntimeError(msg) from exc
    return pa, pc, pq


# Column order we use internally for interval tuples.
# (min,max) pairs in order: θ₁, φ₁, θ₂, φ₂, α
INTERVAL_COLS = [
    "T1_min",
    "T1_max",
    "V1_min",
    "V1_max",
    "T2_min",
    "T2_max",
    "V2_min",
    "V2_max",
    "A_min",
    "A_max",
]


PARAMS = ["θ₁", "φ₁", "θ₂", "φ₂", "α"]


def _split_param_from_code(code: int) -> int:
    if code not in (1, 2, 3, 4, 5):
        raise ValueError(f"unexpected split code: {code}")
    return code - 1


def _parts_for_split_code(code: int) -> int:
    # Empirically (from solution_tree.parquet):
    #   split=1 -> 4, split=2 -> 30, split=3 -> 4, split=4 -> 15, split=5 -> 30, split=6 -> 32
    if code == 1:
        return 4
    if code == 2:
        return 30
    if code == 3:
        return 4
    if code == 4:
        return 15
    if code == 5:
        return 30
    raise ValueError(f"unexpected split code: {code}")


IntervalTuple = tuple[int, int, int, int, int, int, int, int, int, int]


def _interval_to_arrays(iv: IntervalTuple) -> tuple[list[int], list[int]]:
    mins = [iv[0], iv[2], iv[4], iv[6], iv[8]]
    maxs = [iv[1], iv[3], iv[5], iv[7], iv[9]]
    return mins, maxs


def _arrays_to_interval(mins: list[int], maxs: list[int]) -> IntervalTuple:
    return (
        mins[0],
        maxs[0],
        mins[1],
        maxs[1],
        mins[2],
        maxs[2],
        mins[3],
        maxs[3],
        mins[4],
        maxs[4],
    )


def _split_into_parts(iv: IntervalTuple, param_idx: int, parts: int) -> list[IntervalTuple]:
    mins, maxs = _interval_to_arrays(iv)
    lo = mins[param_idx]
    hi = maxs[param_idx]
    step = (hi - lo) // parts
    out: list[IntervalTuple] = []
    for i in range(parts):
        mins2 = list(mins)
        maxs2 = list(maxs)
        mins2[param_idx] = lo + i * step
        maxs2[param_idx] = lo + (i + 1) * step
        out.append(_arrays_to_interval(mins2, maxs2))
    return out


def _lower_half(iv: IntervalTuple, param_idx: int) -> IntervalTuple:
    mins, maxs = _interval_to_arrays(iv)
    mid = (mins[param_idx] + maxs[param_idx]) // 2
    maxs[param_idx] = mid
    return _arrays_to_interval(mins, maxs)


def _upper_half(iv: IntervalTuple, param_idx: int) -> IntervalTuple:
    mins, maxs = _interval_to_arrays(iv)
    mid = (mins[param_idx] + maxs[param_idx]) // 2
    mins[param_idx] = mid
    return _arrays_to_interval(mins, maxs)


def _cube_fold_halves(iv: IntervalTuple, param_order: Iterable[int]) -> list[IntervalTuple]:
    # Matches the Lean `cubeFold [lower_half, upper_half] iv params` order:
    # for each param in order, expand each interval into lower then upper.
    intervals = [iv]
    for p in param_order:
        nxt: list[IntervalTuple] = []
        for cur in intervals:
            nxt.append(_lower_half(cur, p))
            nxt.append(_upper_half(cur, p))
        intervals = nxt
    return intervals


@dataclasses.dataclass(frozen=True)
class Expectation:
    parent_id: int
    desc: str
    expected: IntervalTuple


def _fmt_iv(iv: IntervalTuple) -> str:
    mins, maxs = _interval_to_arrays(iv)
    parts = [f"{p}=[{a},{b}]" for p, a, b in zip(PARAMS, mins, maxs, strict=True)]
    return " ".join(parts)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Best-effort validation that nodeType=3 split nodes in solution_tree.parquet "
            "have children intervals matching the intended split semantics."
        )
    )
    parser.add_argument(
        "--parquet",
        type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.parquet"),
        help="Path to solution_tree.parquet.",
    )
    parser.add_argument(
        "--max-parents",
        type=int,
        default=2_000,
        help="Check only the first N split nodes (nodeType=3). Use 0 for all.",
    )
    parser.add_argument(
        "--max-gap",
        type=int,
        default=250_000,
        help="Skip split nodes whose (IDfirstChild-ID) exceeds this (use 0 for no limit).",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=250_000,
        help="Parquet batch size.",
    )
    parser.add_argument(
        "--progress",
        action="store_true",
        help="Print periodic progress.",
    )
    args = parser.parse_args()

    parquet_path: pathlib.Path = args.parquet
    if not parquet_path.exists():
        print(f"error: parquet file not found: {parquet_path}", file=sys.stderr)
        return 2

    pa, pc, pq = _require_pyarrow()

    pf = pq.ParquetFile(str(parquet_path))
    total_rows = int(pf.metadata.num_rows)

    cols = ["nodeType", "ID", "nrChildren", "IDfirstChild", "split", *INTERVAL_COLS]

    pending: dict[int, Expectation] = {}
    parents_checked = 0
    parents_skipped_gap = 0
    parents_skipped_limit = 0

    param_order_full = [0, 1, 2, 3, 4]  # θ₁, φ₁, θ₂, φ₂, α

    next_progress = 0
    row_offset = 0

    for batch in pf.iter_batches(columns=cols, batch_size=args.batch_size):
        node_type = batch.column(0).to_numpy(zero_copy_only=False)
        ids = batch.column(1).to_numpy(zero_copy_only=False).astype(int)
        nr_children = batch.column(2).to_numpy(zero_copy_only=False)
        first_child = batch.column(3).to_numpy(zero_copy_only=False)
        split = batch.column(4).to_numpy(zero_copy_only=False)
        interval_cols = [batch.column(5 + i).to_numpy(zero_copy_only=False).astype(int) for i in range(len(INTERVAL_COLS))]

        batch_len = len(ids)

        # sanity: IDs are sequential, but keep the check cheap.
        if ids[0] != row_offset:
            print(f"error: unexpected ID sequence at offset {row_offset}: saw {ids[0]}", file=sys.stderr)
            return 2

        def interval_at(i: int) -> IntervalTuple:
            return tuple(col[i] for col in interval_cols)  # type: ignore[return-value]

        # Step 1: resolve any pending expectations that fall within this batch.
        if pending:
            lo = row_offset
            hi = row_offset + batch_len
            for child_id in sorted([k for k in pending.keys() if lo <= k < hi]):
                exp = pending.pop(child_id)
                idx = child_id - lo
                actual = interval_at(idx)
                if actual != exp.expected:
                    print("split mismatch:", file=sys.stderr)
                    print(f"  child_id={child_id}", file=sys.stderr)
                    print(f"  parent_id={exp.parent_id} ({exp.desc})", file=sys.stderr)
                    print(f"  expected: {_fmt_iv(exp.expected)}", file=sys.stderr)
                    print(f"  actual:   {_fmt_iv(actual)}", file=sys.stderr)
                    return 1

        # Step 2: process split nodes in this batch, in increasing ID order.
        if args.max_parents == 0 or parents_checked < args.max_parents:
            split_idxs = [i for i in range(batch_len) if int(node_type[i]) == 3]
        else:
            split_idxs = []

        for i in split_idxs:
            rid = int(ids[i])

            if args.max_parents != 0 and parents_checked >= args.max_parents:
                parents_skipped_limit += 1
                continue

            fc = first_child[i]
            sp = split[i]
            nc = nr_children[i]
            if fc is None or sp is None or nc is None:
                print(f"error: split node missing fields at ID={rid}", file=sys.stderr)
                return 2

            fc = int(fc)
            sp = int(sp)
            nc = int(nc)
            gap = fc - rid
            if args.max_gap and gap > args.max_gap:
                parents_skipped_gap += 1
                continue

            if fc <= rid:
                print(f"error: IDfirstChild not greater than parent at ID={rid} child={fc}", file=sys.stderr)
                return 2

            parent_iv = interval_at(i)

            if sp == 6:
                if nc != 32:
                    print(f"error: split=6 but nrChildren={nc} at ID={rid}", file=sys.stderr)
                    return 2
                expected_children = _cube_fold_halves(parent_iv, param_order_full)
                if len(expected_children) != 32:
                    raise AssertionError("expected 32 children from cube fold")
            else:
                param_idx = _split_param_from_code(sp)
                parts = _parts_for_split_code(sp)
                if nc != parts:
                    print(f"error: split={sp} expected nrChildren={parts} but saw {nc} at ID={rid}", file=sys.stderr)
                    return 2
                expected_children = _split_into_parts(parent_iv, param_idx, parts)

            last_child = fc + len(expected_children) - 1
            if last_child >= total_rows:
                print(
                    f"error: child index out of range at ID={rid}: fc={fc} count={len(expected_children)} total={total_rows}",
                    file=sys.stderr,
                )
                return 2

            desc = f"split={sp} nrChildren={nc}"
            for k, child_iv in enumerate(expected_children):
                child_id = fc + k
                if row_offset <= child_id < row_offset + batch_len:
                    idx = child_id - row_offset
                    actual = interval_at(idx)
                    if actual != child_iv:
                        print("split mismatch:", file=sys.stderr)
                        print(f"  child_id={child_id}", file=sys.stderr)
                        print(f"  parent_id={rid} ({desc})", file=sys.stderr)
                        print(f"  expected: {_fmt_iv(child_iv)}", file=sys.stderr)
                        print(f"  actual:   {_fmt_iv(actual)}", file=sys.stderr)
                        return 1
                else:
                    if child_id in pending:
                        print(f"error: duplicate expectation for child ID {child_id}", file=sys.stderr)
                        return 2
                    pending[child_id] = Expectation(parent_id=rid, desc=desc, expected=child_iv)

            parents_checked += 1

        row_offset += batch_len

        if args.progress and row_offset >= next_progress:
            next_progress = row_offset + 1_000_000
            print(
                f"progress: rows={row_offset}/{total_rows} parents_checked={parents_checked} pending={len(pending)}",
                file=sys.stderr,
            )

        # Early exit: we’ve checked all requested parents and no pending expectations remain.
        if (args.max_parents != 0 and parents_checked >= args.max_parents) and not pending:
            break

    if pending:
        print(f"error: finished scan with {len(pending)} pending expectations", file=sys.stderr)
        # Print a few for debugging.
        for child_id in sorted(pending.keys())[:10]:
            exp = pending[child_id]
            print(f"  child_id={child_id} parent_id={exp.parent_id} {exp.desc}", file=sys.stderr)
        return 1

    print("ok:")
    print(f"  parents_checked={parents_checked}")
    if args.max_parents != 0:
        print(f"  parents_skipped_limit={parents_skipped_limit}")
    if args.max_gap:
        print(f"  parents_skipped_gap={parents_skipped_gap}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
