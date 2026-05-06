import Noperthedron

open Noperthedron.Solution

private partial def checkRowsLoop (table : Table) (i : ℕ)
    (acc : ∀ j : Fin table.size, j.val < i → table[j].ValidIx table j) :
    IO (PLift table.RowsValid) := do
  if h : i < table.size then
    let row := table[i]
    let row_type_str :=
      match row.nodeType with
      | 1 => "global"
      | 2 => "local"
      | 3 => "split"
      | _ => "unknown"
    if h_valid : row.ValidIx table i then
      IO.println s!"row {i} [{row_type_str}]: valid"
      let acc' : ∀ j : Fin table.size, j.val < i + 1 → table[j].ValidIx table j := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · exact acc j hj'
        · have heq : j = ⟨i, h⟩ := Fin.ext hj'
          subst heq
          exact h_valid
      checkRowsLoop table (i + 1) acc'
    else
      IO.println s!"row {i} [{row_type_str}]: INVALID"
      throw (IO.userError s!"row {i} is invalid")
  else
    return PLift.up fun j => acc j (Nat.lt_of_lt_of_le j.isLt (Nat.le_of_not_lt h))

unsafe def main (args : List String) : IO Unit := do
  let csv_filepath ←
    match args with
    | [arg] => pure arg
    | _ => throw (IO.userError "expects exactly one argument")

  let table ← readSolutionTable csv_filepath
  IO.println s!"parsing done!"

  let h_valid_lifted ← checkRowsLoop table 0 (fun _ hj => absurd hj (Nat.not_lt_zero _))
  let h_valid := h_valid_lifted.down

  if h_nonempty : 0 < table.size then
    if h_first : table[0].interval = rowZero.interval then
      let _validTable : ValidTable := {
        table := table
        rows_valid := h_valid
        nonempty := h_nonempty
        contains_tightInterval := by
          rw [show (table[0].interval : Set (Pose ℝ)) = (rowZero.interval : Set (Pose ℝ))
              from by rw [h_first]]
          exact rowZero_contains_tightInterval
      }
      IO.println s!"ValidTable constructed with {table.size} rows."
    else
      throw (IO.userError "table[0].interval does not match rowZero.interval")
  else
    throw (IO.userError "table is empty")
