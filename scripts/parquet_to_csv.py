#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import sys


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


def _require_pyarrow() -> tuple[object, object, object]:
    try:
        import pyarrow as pa  # noqa: F401
        import pyarrow.csv as pacsv  # noqa: F401
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
    return pa, pacsv, pq


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Convert Rupert's solution_tree.parquet into a CSV with only the columns "
            "needed for the Lean `Solution.Row` schema."
        )
    )
    parser.add_argument(
        "--parquet",
        type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.parquet"),
        help="Path to solution_tree.parquet (default: external/rupert/data/solution_tree.parquet).",
    )
    parser.add_argument(
        "--out",
        type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.skinny.csv"),
        help="Output CSV path (default: external/rupert/data/solution_tree.skinny.csv).",
    )
    parser.add_argument(
        "--columns",
        nargs="+",
        default=list(DEFAULT_COLUMNS),
        help="Columns to export (defaults to a Lean-oriented subset).",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=50_000,
        help="Row batch size for streaming conversion (default: 50000).",
    )
    args = parser.parse_args()

    pa, pacsv, pq = _require_pyarrow()

    parquet_path: pathlib.Path = args.parquet
    out_path: pathlib.Path = args.out
    columns: list[str] = list(args.columns)

    if not parquet_path.exists():
        print(f"error: parquet file not found: {parquet_path}", file=sys.stderr)
        return 2

    out_path.parent.mkdir(parents=True, exist_ok=True)

    parquet_file = pq.ParquetFile(str(parquet_path))
    write_opts = pacsv.WriteOptions(include_header=True)

    total = 0
    with out_path.open("wb") as f:
        first = True
        for batch in parquet_file.iter_batches(columns=columns, batch_size=args.batch_size):
            table = pa.Table.from_batches([batch])
            if first:
                pacsv.write_csv(table, f, write_options=write_opts)
                first = False
            else:
                pacsv.write_csv(table, f, write_options=pacsv.WriteOptions(include_header=False))
            total += table.num_rows

    print(f"ok: wrote {total} rows to {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
