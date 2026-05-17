#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import sys


def _require_pyarrow() -> tuple[object, object]:
    try:
        import pyarrow as pa  # noqa: F401
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
    return pa, pq


def _decode_i(idx: int) -> int:
    # idx = k + 15*i + 45*l, where:
    #   k ∈ {0..14}, i ∈ {0,1,2}, l ∈ {0,1}
    return (idx % 45) // 15


def _decode_k(idx: int) -> int:
    return idx % 15


def _decode_l(idx: int) -> int:
    return idx // 45


def _check_row(p: tuple[int, int, int], q: tuple[int, int, int]) -> tuple[bool, int, int, int]:
    """
    Return (ok, reflect, dk, dl) for the dihedral-style congruence witness:
      - dl is the sign flip on `l` (i.e. multiply by -1 if dl=1),
      - reflect=0 means k ↦ k + dk,
      - reflect=1 means k ↦ -k + dk.
    """
    # All indices should be within the 90-vertex encoding.
    if any(x < 0 or x >= 90 for x in (*p, *q)):
        return False, 0, 0, 0

    # Orbit must match position-wise (dataset uses consistent ordering).
    ip = [_decode_i(x) for x in p]
    iq = [_decode_i(x) for x in q]
    if ip != iq:
        return False, 0, 0, 0

    # l-parity offset (mod 2).
    lp = [_decode_l(x) for x in p]
    lq = [_decode_l(x) for x in q]
    dl = lp[0] ^ lq[0]
    if [a ^ dl for a in lq] != lp:
        return False, 0, 0, 0

    kp = [_decode_k(x) for x in p]
    kq = [_decode_k(x) for x in q]

    # Try rotation: k ↦ k + dk.
    dk = (kp[0] - kq[0]) % 15
    if [(a + dk) % 15 for a in kq] == kp:
        return True, 0, dk, dl

    # Try reflection: k ↦ -k + dk.
    dk = (kp[0] + kq[0]) % 15
    if [(dk - a) % 15 for a in kq] == kp:
        return True, 1, dk, dl

    return False, 0, 0, 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Best-effort validation that each nodeType=2 row's (P,Q) indices are related by a simple\n"
            "dihedral-style symmetry on the 15-fold rotation index (plus optional global sign flip).\n"
            "This matches the empirical structure in `solution_tree.parquet` and is a good bridge toward\n"
            "a decidable Lean-side congruence checker."
        )
    )
    parser.add_argument(
        "--parquet",
        type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.parquet"),
        help="Path to solution_tree.parquet.",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=250_000,
        help="Parquet batch size.",
    )
    parser.add_argument(
        "--max-rows",
        type=int,
        default=0,
        help="Check only the first N local rows (nodeType=2). Use 0 for all.",
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

    pa, pq = _require_pyarrow()

    pf = pq.ParquetFile(str(parquet_path))
    cols = [
        "nodeType",
        "ID",
        "P1_index",
        "P2_index",
        "P3_index",
        "Q1_index",
        "Q2_index",
        "Q3_index",
    ]

    total = 0
    ok = 0
    reflect_counts: dict[int, int] = {0: 0, 1: 0}
    dl_counts: dict[int, int] = {0: 0, 1: 0}
    dk_counts: dict[tuple[int, int], int] = {}
    bad_examples: list[dict[str, object]] = []

    row_offset = 0

    for batch in pf.iter_batches(columns=cols, batch_size=args.batch_size):
        node_type = batch.column(0).to_numpy(zero_copy_only=False)
        ids = batch.column(1).to_numpy(zero_copy_only=False).astype(int)
        p1 = batch.column(2).to_numpy(zero_copy_only=False)
        p2 = batch.column(3).to_numpy(zero_copy_only=False)
        p3 = batch.column(4).to_numpy(zero_copy_only=False)
        q1 = batch.column(5).to_numpy(zero_copy_only=False)
        q2 = batch.column(6).to_numpy(zero_copy_only=False)
        q3 = batch.column(7).to_numpy(zero_copy_only=False)

        # Cheap sanity: IDs are sequential.
        if ids[0] != row_offset:
            print(f"error: unexpected ID sequence at offset {row_offset}: saw {ids[0]}", file=sys.stderr)
            return 2
        row_offset += len(ids)

        for nt, rid, a, b, c, d, e, f in zip(node_type, ids, p1, p2, p3, q1, q2, q3, strict=True):
            if int(nt) != 2:
                continue
            total += 1
            good, reflect, dk, dl = _check_row((int(a), int(b), int(c)), (int(d), int(e), int(f)))
            if good:
                ok += 1
                reflect_counts[reflect] = reflect_counts.get(reflect, 0) + 1
                dl_counts[dl] = dl_counts.get(dl, 0) + 1
                dk_counts[(reflect, dk)] = dk_counts.get((reflect, dk), 0) + 1
            elif len(bad_examples) < 10:
                bad_examples.append(
                    {
                        "ID": int(rid),
                        "P": (int(a), int(b), int(c)),
                        "Q": (int(d), int(e), int(f)),
                        "decoded_P": [(_decode_i(int(x)), _decode_k(int(x)), _decode_l(int(x))) for x in (int(a), int(b), int(c))],
                        "decoded_Q": [(_decode_i(int(x)), _decode_k(int(x)), _decode_l(int(x))) for x in (int(d), int(e), int(f))],
                    }
                )

            if args.max_rows and total >= args.max_rows:
                break

        if args.progress:
            print(f"progress: checked_local_rows={total} ok={ok}", file=sys.stderr)

        if args.max_rows and total >= args.max_rows:
            break

    if ok != total:
        print(f"FAIL: local congruence check: ok={ok} total={total}", file=sys.stderr)
        if bad_examples:
            print("examples:", file=sys.stderr)
            for ex in bad_examples:
                print(f"  {ex}", file=sys.stderr)
        return 1

    print(f"ok: local congruence check passed: ok={ok} total={total}")
    print(f"reflect_counts={reflect_counts}  # reflect=1 means k ↦ -k + dk")
    print(f"dl_counts={dl_counts}  # dl=1 means global sign flip (-I)")
    print("top dk (reflect,dk) counts:")
    for (reflect, dk), n in sorted(dk_counts.items(), key=lambda kv: (-kv[1], kv[0]))[:20]:
        print(f"  ({reflect},{dk}): {n}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

