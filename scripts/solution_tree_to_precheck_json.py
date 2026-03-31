#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any


DEFAULT_COLUMNS = [
    "ID",
    "nodeType",
    "nrChildren",
    "IDfirstChild",
    "split",
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
    "P1_index",
    "P2_index",
    "P3_index",
    "Q1_index",
    "Q2_index",
    "Q3_index",
    "r",
    "sigma_Q",
    "wx_nominator",
    "wy_nominator",
    "w_denominator",
    "S_index",
]

DENOM_Z = 15_360_000
FOUR_BOUND_Z = 8 * DENOM_Z


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


def _rat(num: int, den: int) -> dict[str, Any]:
    return {"num": int(num), "den": int(den)}


def _vec3(num: int, den: int) -> list[dict[str, Any]]:
    return [_rat(num, den), _rat(0, 1), _rat(0, 1)]


def _init_local_ok() -> dict[str, list[bool]]:
    return {
        "bound_r_ok": [],
        "bound_delta_ok": [],
        "ae1_ok": [],
        "ae2_ok": [],
        "span1_ok": [],
        "span2_ok": [],
        "be_ok": [],
    }


def _get_int(row: dict[str, Any], key: str, default: int = 0) -> int:
    val = row.get(key)
    if val is None:
        return default
    return int(val)


def _mid_in_four(row: dict[str, Any]) -> bool:
    for p in ("T1", "V1", "T2", "V2", "A"):
        lo = _get_int(row, f"{p}_min")
        hi = _get_int(row, f"{p}_max")
        mid = lo + hi
        if mid < -FOUR_BOUND_Z or mid > FOUR_BOUND_Z:
            return False
    return True


def _eps_pos(row: dict[str, Any]) -> bool:
    for p in ("T1", "V1", "T2", "V2", "A"):
        lo = _get_int(row, f"{p}_min")
        hi = _get_int(row, f"{p}_max")
        if hi - lo > 0:
            return True
    return False


def _r_pos(row: dict[str, Any]) -> bool:
    r = row.get("r")
    if r is None:
        return False
    return int(r) > 0


def _w_unit(row: dict[str, Any]) -> bool:
    den = row.get("w_denominator")
    wx = row.get("wx_nominator")
    wy = row.get("wy_nominator")
    if den is None or wx is None or wy is None:
        return False
    den = int(den)
    wx = int(wx)
    wy = int(wy)
    return den != 0 and wx * wx + wy * wy == den * den


def _decode_i(idx: int) -> int:
    return (idx % 45) // 15


def _decode_k(idx: int) -> int:
    return idx % 15


def _decode_l(idx: int) -> int:
    return idx // 45


def _congruence_ok(row: dict[str, Any]) -> bool:
    p = (_get_int(row, "P1_index"), _get_int(row, "P2_index"), _get_int(row, "P3_index"))
    q = (_get_int(row, "Q1_index"), _get_int(row, "Q2_index"), _get_int(row, "Q3_index"))
    if not all(0 <= v < 90 for v in (*p, *q)):
        return False
    if not (_decode_i(p[0]) == _decode_i(q[0]) and _decode_i(p[1]) == _decode_i(q[1]) and _decode_i(p[2]) == _decode_i(q[2])):
        return False
    dl = (_decode_l(p[0]) + _decode_l(q[0])) % 2
    if not ((_decode_l(q[0]) + dl) % 2 == _decode_l(p[0]) and (_decode_l(q[1]) + dl) % 2 == _decode_l(p[1]) and (_decode_l(q[2]) + dl) % 2 == _decode_l(p[2])):
        return False
    dk_rot = (_decode_k(p[0]) + 15 - _decode_k(q[0])) % 15
    dk_ref = (_decode_k(p[0]) + _decode_k(q[0])) % 15
    rot_ok = (
        (_decode_k(q[0]) + dk_rot) % 15 == _decode_k(p[0])
        and (_decode_k(q[1]) + dk_rot) % 15 == _decode_k(p[1])
        and (_decode_k(q[2]) + dk_rot) % 15 == _decode_k(p[2])
    )
    ref_ok = (
        (dk_ref + 15 - _decode_k(q[0])) % 15 == _decode_k(p[0])
        and (dk_ref + 15 - _decode_k(q[1])) % 15 == _decode_k(p[1])
        and (dk_ref + 15 - _decode_k(q[2])) % 15 == _decode_k(p[2])
        and _decode_i(p[0]) == _decode_i(p[1])
        and _decode_i(p[0]) == _decode_i(p[2])
    )
    return rot_ok or ref_ok


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Export solution_tree.parquet into JSON for Lean precheck stubs."
    )
    parser.add_argument(
        "--parquet",
        type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.parquet"),
        help="Path to solution_tree.parquet.",
    )
    parser.add_argument(
        "--out",
        type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.precheck.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=1000,
        help="Number of rows to export (default: 1000).",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=50_000,
        help="Parquet batch size.",
    )
    args = parser.parse_args()

    parquet_path: pathlib.Path = args.parquet
    if not parquet_path.exists():
        print(f"error: parquet file not found: {parquet_path}", file=sys.stderr)
        return 2

    pa, pq = _require_pyarrow()
    pf = pq.ParquetFile(str(parquet_path))

    rows: list[dict[str, Any]] = []
    remaining = args.limit
    for batch in pf.iter_batches(columns=DEFAULT_COLUMNS, batch_size=args.batch_size):
        table = pa.Table.from_batches([batch])
        for record in table.to_pylist():
            rows.append(record)
            remaining -= 1
            if remaining <= 0:
                break
        if remaining <= 0:
            break

    n = len(rows)
    local_ok = _init_local_ok()
    global_ok = {
        "S": [_vec3(1, 1)] * n,
        "exceeds_ok": [],
    }
    congruence_ok: list[bool] = []

    for row in rows:
        node_type = int(row.get("nodeType") or 0)
        basic_local = _mid_in_four(row) and _eps_pos(row) and _r_pos(row)
        basic_global = _mid_in_four(row) and _eps_pos(row) and _w_unit(row)
        if node_type == 2:
            for key in local_ok:
                local_ok[key].append(basic_local)
        else:
            for key in local_ok:
                local_ok[key].append(True)
        if node_type == 1:
            global_ok["exceeds_ok"].append(basic_global)
        else:
            global_ok["exceeds_ok"].append(True)
        congruence_ok.append(_congruence_ok(row) if node_type == 2 else True)

    out = {
        "rows": rows,
        "local_ok": local_ok,
        "global_ok": global_ok,
        "congruence_ok": congruence_ok,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as f:
        json.dump(out, f)

    print(f"ok: wrote {n} rows to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
