import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.Vertices.Exact

namespace Noperthedron

theorem exists_solution_table :
    ∃ (tab : Solution.Table) (tab_valid : tab.Valid)
      (hz : 0 < tab.size),
      (tightInterval : Set Pose) ⊆ (tab[0].interval : Set Pose)
     := by
  sorry -- TODO(hard)
