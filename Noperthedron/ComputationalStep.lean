import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.Vertices.Exact

namespace Noperthedron

theorem exists_solution_table :
    ∃ (tab : Solution.Table) (tab_valid : tab.Valid)
      (hz : 0 < tab.size),
      (tightInterval : Set (Pose ℝ)) ⊆ (tab[0].interval : Set (Pose ℝ))
     := by
  sorry -- TODO(hard)
