import Noperthedron.Checker.RowZero
import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.SolutionTable.Parse
import Noperthedron.Vertices.Exact

/-!
  Expensive computational step. We expect this to take at least 40 hours to complete.

  `constructValidTable.lean` establishes the same result via an executable program.
-/

namespace Noperthedron

theorem exists_solution_table : ∃ (tab : Solution.ValidTable), True := by
  sorry
  -- Currently, the below seems to be much less efficient than the equivalent
  -- logic in contructValidTable.lean. Can we improve it somehow?
  /-
  let solution_csv : String :=
    -- unzipped from https://github.com/Jakob256/Rupert/blob/main/data/solution_tree.zip
    include_str "../../noperthedron-verification-py/data/solution_tree.csv"
  let tab := match Solution.parseSolutionTable solution_csv with
             | .ok s => s
             | .error _ => #[]
  have hnonempty : 0 < tab.size := by native_decide
  have hrowzero : tab[0].interval = Solution.rowZero.interval := by native_decide
  have hvalid : tab.RowsValid := by native_decide
  refine ⟨⟨tab, hvalid, hnonempty, ?_⟩, ⟨⟩⟩
  rw [hrowzero]
  exact Solution.rowZero_contains_tightInterval
  -/
