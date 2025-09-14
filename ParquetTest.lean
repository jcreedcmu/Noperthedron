import Parquet

def main : IO Unit := do
  let _parquet ← readParquetFile "/home/jcreed/pgit/Rupert/data/solution_tree.parquet"
  return Unit.unit
