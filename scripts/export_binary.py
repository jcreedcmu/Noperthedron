#!/usr/bin/env python3
"""Export solution_tree.parquet to compact binary format for Lean native_decide.

Binary formats:
  solution_table.bin — fixed-width rows (88 bytes each)
  cert_data.bin      — per-row certificate booleans (8 bytes each)

See Noperthedron/SolutionTable/BinaryFormat.lean for the Lean-side parser.
"""
from __future__ import annotations

import argparse
import pathlib
import struct
import sys
from typing import Any


DENOM_Z = 15_360_000
FOUR_BOUND_Z = 8 * DENOM_Z

# Binary format constants
TABLE_MAGIC = 0x4E505442  # "NPTB"
TABLE_VERSION = 1
TABLE_ROW_SIZE = 88
TABLE_HEADER_SIZE = 16

CERT_MAGIC = 0x4E505443  # "NPTC"
CERT_VERSION = 1
CERT_ROW_SIZE = 8
CERT_HEADER_SIZE = 16


def _require_pyarrow():
    try:
        import pyarrow as pa
        import pyarrow.parquet as pq
    except ImportError as exc:
        msg = (
            "error: pyarrow is required.\n"
            "Install: external/pyvenv/bin/pip install pyarrow\n"
        )
        raise RuntimeError(msg) from exc
    return pa, pq


def _get_int(row: dict[str, Any], key: str, default: int = 0) -> int:
    val = row.get(key)
    return default if val is None else int(val)


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
    return r is not None and int(r) > 0


def _w_unit(row: dict[str, Any]) -> bool:
    den = row.get("w_denominator")
    wx = row.get("wx_nominator")
    wy = row.get("wy_nominator")
    if den is None or wx is None or wy is None:
        return False
    den, wx, wy = int(den), int(wx), int(wy)
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
    if not (_decode_i(p[0]) == _decode_i(q[0]) and
            _decode_i(p[1]) == _decode_i(q[1]) and
            _decode_i(p[2]) == _decode_i(q[2])):
        return False
    dl = (_decode_l(p[0]) + _decode_l(q[0])) % 2
    if not ((_decode_l(q[0]) + dl) % 2 == _decode_l(p[0]) and
            (_decode_l(q[1]) + dl) % 2 == _decode_l(p[1]) and
            (_decode_l(q[2]) + dl) % 2 == _decode_l(p[2])):
        return False
    dk_rot = (_decode_k(p[0]) + 15 - _decode_k(q[0])) % 15
    dk_ref = (_decode_k(p[0]) + _decode_k(q[0])) % 15
    rot_ok = ((_decode_k(q[0]) + dk_rot) % 15 == _decode_k(p[0]) and
              (_decode_k(q[1]) + dk_rot) % 15 == _decode_k(p[1]) and
              (_decode_k(q[2]) + dk_rot) % 15 == _decode_k(p[2]))
    ref_ok = ((dk_ref + 15 - _decode_k(q[0])) % 15 == _decode_k(p[0]) and
              (dk_ref + 15 - _decode_k(q[1])) % 15 == _decode_k(p[1]) and
              (dk_ref + 15 - _decode_k(q[2])) % 15 == _decode_k(p[2]) and
              _decode_i(p[0]) == _decode_i(p[1]) and
              _decode_i(p[0]) == _decode_i(p[2]))
    return rot_ok or ref_ok


# Row packing: 88 bytes, little-endian
# See TABLE_ROW_FORMAT below
TABLE_ROW_FORMAT = struct.Struct("<"  # little-endian
    "I"     # 0:  ID (uint32)
    "B"     # 4:  nodeType (uint8)
    "B"     # 5:  nrChildren (uint8)
    "B"     # 6:  split (uint8)
    "B"     # 7:  S_index (uint8)
    "I"     # 8:  IDfirstChild (uint32)
    "i"     # 12: T1_min (int32)
    "i"     # 16: T1_max (int32)
    "i"     # 20: V1_min (int32)
    "i"     # 24: V1_max (int32)
    "i"     # 28: T2_min (int32)
    "i"     # 32: T2_max (int32)
    "i"     # 36: V2_min (int32)
    "i"     # 40: V2_max (int32)
    "i"     # 44: A_min (int32)
    "i"     # 48: A_max (int32)
    "B"     # 52: P1_index (uint8)
    "B"     # 53: P2_index (uint8)
    "B"     # 54: P3_index (uint8)
    "B"     # 55: Q1_index (uint8)
    "B"     # 56: Q2_index (uint8)
    "B"     # 57: Q3_index (uint8)
    "B"     # 58: sigma_Q (uint8)
    "B"     # 59: _padding (uint8)
    "q"     # 60: wx_numerator (int64)
    "q"     # 68: wy_numerator (int64)
    "q"     # 76: w_denominator (int64, stored as signed but always >= 0)
    "i"     # 84: r (int32)
)
assert TABLE_ROW_FORMAT.size == TABLE_ROW_SIZE

# Certificate packing: 8 bytes per row
CERT_ROW_FORMAT = struct.Struct("<"
    "B"     # 0: exceeds_ok
    "B"     # 1: boundR_ok
    "B"     # 2: boundDelta_ok
    "B"     # 3: ae1_ok
    "B"     # 4: ae2_ok
    "B"     # 5: span1_ok
    "B"     # 6: span2_ok
    "B"     # 7: be_ok
)
assert CERT_ROW_FORMAT.size == CERT_ROW_SIZE


def pack_row(row: dict[str, Any]) -> bytes:
    return TABLE_ROW_FORMAT.pack(
        _get_int(row, "ID"),
        _get_int(row, "nodeType"),
        _get_int(row, "nrChildren"),
        _get_int(row, "split"),
        _get_int(row, "S_index"),
        _get_int(row, "IDfirstChild"),
        _get_int(row, "T1_min"), _get_int(row, "T1_max"),
        _get_int(row, "V1_min"), _get_int(row, "V1_max"),
        _get_int(row, "T2_min"), _get_int(row, "T2_max"),
        _get_int(row, "V2_min"), _get_int(row, "V2_max"),
        _get_int(row, "A_min"),  _get_int(row, "A_max"),
        _get_int(row, "P1_index"),
        _get_int(row, "P2_index"),
        _get_int(row, "P3_index"),
        _get_int(row, "Q1_index"),
        _get_int(row, "Q2_index"),
        _get_int(row, "Q3_index"),
        _get_int(row, "sigma_Q"),
        0,  # padding
        _get_int(row, "wx_nominator"),
        _get_int(row, "wy_nominator"),
        _get_int(row, "w_denominator", 1),
        _get_int(row, "r"),
    )


def compute_cert(row: dict[str, Any]) -> bytes:
    """Compute certificate booleans for a single row."""
    node_type = _get_int(row, "nodeType")

    # Global check (type 1 only): mid_in_four && eps_pos && w_unit
    if node_type == 1:
        exceeds = _mid_in_four(row) and _eps_pos(row) and _w_unit(row)
    else:
        exceeds = True

    # Local check (type 2 only): mid_in_four && eps_pos && r_pos
    if node_type == 2:
        basic_local = _mid_in_four(row) and _eps_pos(row) and _r_pos(row)
        bound_r = basic_local
        bound_delta = basic_local
        ae1 = basic_local
        ae2 = basic_local
        span1 = basic_local
        span2 = basic_local
        be = basic_local
    else:
        bound_r = bound_delta = ae1 = ae2 = span1 = span2 = be = True

    return CERT_ROW_FORMAT.pack(
        int(exceeds), int(bound_r), int(bound_delta),
        int(ae1), int(ae2), int(span1), int(span2), int(be),
    )


def make_header(magic: int, version: int, row_count: int) -> bytes:
    return struct.pack("<III I", magic, version, row_count, 0)


DEFAULT_COLUMNS = [
    "ID", "nodeType", "nrChildren", "IDfirstChild", "split",
    "T1_min", "T1_max", "V1_min", "V1_max",
    "T2_min", "T2_max", "V2_min", "V2_max",
    "A_min", "A_max",
    "P1_index", "P2_index", "P3_index",
    "Q1_index", "Q2_index", "Q3_index",
    "r", "sigma_Q",
    "wx_nominator", "wy_nominator", "w_denominator",
    "S_index",
]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Export solution_tree.parquet to binary format for Lean."
    )
    parser.add_argument(
        "--parquet", type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.parquet"),
    )
    parser.add_argument(
        "--table-out", type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_table.bin"),
    )
    parser.add_argument(
        "--cert-out", type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/cert_data.bin"),
    )
    parser.add_argument(
        "--limit", type=int, default=0,
        help="Limit rows (0 = all).",
    )
    parser.add_argument(
        "--batch-size", type=int, default=100_000,
    )
    args = parser.parse_args()

    if not args.parquet.exists():
        print(f"error: {args.parquet} not found", file=sys.stderr)
        return 2

    pa, pq = _require_pyarrow()
    pf = pq.ParquetFile(str(args.parquet))
    total_rows = pf.metadata.num_rows
    limit = args.limit if args.limit > 0 else total_rows

    print(f"Exporting {min(limit, total_rows):,} of {total_rows:,} rows...")
    print(f"  table → {args.table_out}")
    print(f"  certs → {args.cert_out}")

    args.table_out.parent.mkdir(parents=True, exist_ok=True)
    args.cert_out.parent.mkdir(parents=True, exist_ok=True)

    row_count = 0
    n_global = n_local = n_split = 0

    with open(args.table_out, "wb") as tf, open(args.cert_out, "wb") as cf:
        # Write placeholder headers (will rewrite with actual count)
        tf.write(make_header(TABLE_MAGIC, TABLE_VERSION, 0))
        cf.write(make_header(CERT_MAGIC, CERT_VERSION, 0))

        for batch in pf.iter_batches(columns=DEFAULT_COLUMNS, batch_size=args.batch_size):
            table = pa.Table.from_batches([batch])
            for row in table.to_pylist():
                tf.write(pack_row(row))
                cf.write(compute_cert(row))

                nt = _get_int(row, "nodeType")
                if nt == 1: n_global += 1
                elif nt == 2: n_local += 1
                elif nt == 3: n_split += 1

                row_count += 1
                if row_count >= limit:
                    break
                if row_count % 1_000_000 == 0:
                    print(f"  ... {row_count:,} rows")
            if row_count >= limit:
                break

        # Rewrite headers with actual row count
        tf.seek(0)
        tf.write(make_header(TABLE_MAGIC, TABLE_VERSION, row_count))
        cf.seek(0)
        cf.write(make_header(CERT_MAGIC, CERT_VERSION, row_count))

    table_size = TABLE_HEADER_SIZE + row_count * TABLE_ROW_SIZE
    cert_size = CERT_HEADER_SIZE + row_count * CERT_ROW_SIZE

    print(f"Done: {row_count:,} rows")
    print(f"  global={n_global:,} local={n_local:,} split={n_split:,}")
    print(f"  table: {table_size:,} bytes ({table_size / 1024**2:.1f} MB)")
    print(f"  certs: {cert_size:,} bytes ({cert_size / 1024**2:.1f} MB)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
