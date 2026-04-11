import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.Vertices.Exact

theorem exists_solution_table :
    ∃ (tab : Solution.Table) (tab_valid : tab.Valid)
      (hz : 0 < tab.size),
      tightInterval ⊆ tab[0].toPoseInterval
     := by
  sorry -- TODO(hard)
