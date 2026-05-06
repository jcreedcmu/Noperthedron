import Noperthedron

/-!
  Program that constructs a `ValidTable` value -- exactly what fits into the "hole" in
  Noperthedron/ProofOfMainTheoremWithHole.lean.
-/

open Noperthedron.Solution

unsafe def main (args : List String) : IO Unit := do
  let csv_filepath ←
    match args with
    | [arg] => pure arg
    | _ => throw (IO.userError "expects exactly one argument")

  let table ← readSolutionTable csv_filepath
  IO.println s!"parsing done!"

  if h_nonempty : 0 < table.size then
    if h_first : table[0].interval = rowZero.interval then
      if h_valid : table.RowsValid then
        let validTable : ValidTable := {
          table := table
          rows_valid := h_valid
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
