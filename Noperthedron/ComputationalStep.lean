import Noperthedron.Checker.RowZero
import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.SolutionTable.Parse
import Noperthedron.Vertices.Exact

namespace Noperthedron

theorem exists_solution_table : ∃ (tab : Solution.ValidTable), True := by
  sorry
  /-
  let solution_csv : String :=
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
