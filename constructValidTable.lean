import Noperthedron.SolutionTable.Check

/-!
  Program that constructs a `ValidTable` value -- exactly what fits into the "hole" in
  Noperthedron/ProofOfMainTheoremWithHole.lean.

  Accepts as input a path to a csv file contains the solution data.

  This runs the same kind of parallel parse-and-check that `native_decide`
  evaluates in VerifiedNative/ComputationalStep.lean, but compiled to native
  code, so it is considerably faster.

  Running on the solution tree from solution_tree_v6.zip takes about 5 minutes on
  a 16-core machine.

  To get the solution tree, make sure you have git-lfs installed and you've fetched
  the full solution_tree_v6.zip file. then unzip it into solution_tree_v6.csv.
-/

open Noperthedron.Solution

def main (args : List String) : IO Unit := do
  let csv_filepath ←
    match args with
    | [arg] => pure arg
    | _ => throw (IO.userError "expects exactly one argument")

  let csv ← IO.FS.readFile csv_filepath
  let table ←
    match parseSolutionTablePar csv 64 with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"parse error: {e}")
  IO.println s!"parsing done! {table.size} rows"

  if h_nonempty : 0 < table.size then
    if h_first : table[0].interval = rowZero.interval then
      if h_valid_b : table.rowsValidParB 512 then
        let validTable : ValidTable := Table.validTableOfChecks h_nonempty h_first h_valid_b
        IO.println s!"ValidTable constructed with {validTable.table.size} rows."
      else
        throw (IO.userError "table rows are not valid")
    else
      throw (IO.userError "table[0].interval does not match rowZero.interval")
  else
    throw (IO.userError "table is empty")
