#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import sys


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


def main() -> int:
    parser = argparse.ArgumentParser(description="Print basic stats for solution_tree.parquet.")
    parser.add_argument(
        "--parquet",
        type=pathlib.Path,
        default=pathlib.Path("external/rupert/data/solution_tree.parquet"),
        help="Path to solution_tree.parquet (default: external/rupert/data/solution_tree.parquet).",
    )
    args = parser.parse_args()

    pa, pc, pq = _require_pyarrow()
    path: pathlib.Path = args.parquet
    if not path.exists():
        print(f"error: parquet file not found: {path}", file=sys.stderr)
        return 2

    pf = pq.ParquetFile(str(path))
    print(f"row_groups={pf.num_row_groups}")
    print(f"rows={pf.metadata.num_rows}")

    cols = ["nodeType", "nrChildren", "split"]
    counts: dict[str, dict[str, int]] = {c: {} for c in cols}

    for batch in pf.iter_batches(columns=cols, batch_size=250_000):
        tbl = pa.Table.from_batches([batch])
        for c in cols:
            vc = pc.value_counts(tbl[c])
            values = vc.field("values").to_pylist()
            freqs = vc.field("counts").to_pylist()
            acc = counts[c]
            for v, n in zip(values, freqs, strict=True):
                key = "null" if v is None else str(v)
                acc[key] = acc.get(key, 0) + int(n)

    for c in cols:
        print(f"\n{c}:")
        for k, n in sorted(counts[c].items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {k}: {n}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
