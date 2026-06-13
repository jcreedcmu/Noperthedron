import Noperthedron.Checker.RowZero
import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Parse

/-!
# Combined solution-table check

A single `Bool`-valued function, `checkSolutionCsv`, that parses the SY25
solution-tree CSV and verifies all the conditions needed to build a
`Solution.ValidTable`, together with its soundness theorem
`checkSolutionCsv_sound`. Bundling everything into one function means a single
`native_decide` invocation (one parse, one pass over the table), and both the
parse and the row checks run in parallel via `Task.spawn`.

The same functions back the `constructValidTable` executable, so a (much
faster, natively compiled) dry run of exactly the code that `native_decide`
will evaluate is available via `lake exe constructValidTable`.
-/

namespace Noperthedron.Solution

/-- Full validity check for a parsed table: nonempty, row 0's interval is
`rowZero.interval` (hence contains `tightInterval`), and every row is valid.
The row checks are split into `nTasks` parallel tasks. -/
def Table.checkFullB (tab : Table) (nTasks : ℕ) : Bool :=
  if h : 0 < tab.size then
    decide (tab[0].interval = rowZero.interval) && tab.rowsValidParB nTasks
  else false

theorem Table.exists_validTable_of_checkFullB {tab : Table} {nTasks : ℕ}
    (h : tab.checkFullB nTasks = true) : ∃ _ : ValidTable, True := by
  unfold Table.checkFullB at h
  split at h
  case isTrue hpos =>
    rw [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨hz, hv⟩ := h
    refine ⟨⟨tab, Table.rowsValid_of_rowsValidParB hv, hpos, ?_⟩, trivial⟩
    rw [show (tab[0].interval : Set (Pose ℝ)) = (rowZero.interval : Set (Pose ℝ))
        from by rw [hz]]
    exact rowZero_contains_tightInterval
  case isFalse => exact absurd h (by simp)

/-- Parse the solution-tree CSV (in `parseTasks` parallel chunks) and check
that the result is a valid table (in `checkTasks` parallel chunks). -/
def checkSolutionCsv (csv : String) (parseTasks checkTasks : ℕ) : Bool :=
  match parseSolutionTablePar csv parseTasks with
  | .error _ => false
  | .ok tab => tab.checkFullB checkTasks

theorem checkSolutionCsv_sound {csv : String} {parseTasks checkTasks : ℕ}
    (h : checkSolutionCsv csv parseTasks checkTasks = true) : ∃ _ : ValidTable, True := by
  unfold checkSolutionCsv at h
  split at h
  · exact absurd h (by simp)
  · exact Table.exists_validTable_of_checkFullB h

/-! ## Smoke tests -/

/-- A 1-row table consisting of a known-valid global leaf. -/
private def testTinyTable : Table := #[{ testGlobalRow with ID := 0 }]

-- The parallel checker accepts a valid table (with the 512 chunks vastly
-- overhanging the 1-row table) and agrees with the sequential decision
-- procedure for `Table.RowsValid`.
/-- info: (true, true) -/
#guard_msgs in
#eval (testTinyTable.rowsValidParB 512, decide testTinyTable.RowsValid)

-- Degenerate parameters: zero tasks must fail the coverage guard on a
-- nonempty table, and must accept the empty table.
/-- info: (false, true) -/
#guard_msgs in
#eval (testTinyTable.rowsValidParB 0, Table.rowsValidParB #[] 0)

end Noperthedron.Solution
