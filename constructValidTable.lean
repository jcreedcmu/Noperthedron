import Noperthedron.SolutionTable.Check

/-!
  Program that constructs a `ValidTable` value -- exactly what fits into the "hole" in
  Noperthedron/ProofOfMainTheoremWithHole.lean.

  Accepts as input a path to a file that contains the unzipped csv from
  https://github.com/Jakob256/Rupert/blob/main/data/solution_tree.zip

  This runs the same parallel parse-and-check functions that `native_decide`
  evaluates in Noperthedron/ComputationalStep.lean, but compiled to native
  code, so it is considerably faster.

  Running this takes about 2.5 hours on a 16-core machine.
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
        let validTable : ValidTable := {
          table := table
          rows_valid := Table.rowsValid_of_rowsValidParB h_valid_b
          nonempty := h_nonempty
          contains_tightInterval := by
            rw [show (table[0].interval : Set (Pose ℝ)) = (rowZero.interval : Set (Pose ℝ))
                from by rw [h_first]]
            exact rowZero_contains_tightInterval
        }
        IO.println s!"ValidTable constructed with {validTable.table.size} rows."
      else
        throw (IO.userError "table rows are not valid")
    else
      throw (IO.userError "table[0].interval does not match rowZero.interval")
  else
    throw (IO.userError "table is empty")
