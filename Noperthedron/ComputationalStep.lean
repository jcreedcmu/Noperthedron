import Noperthedron.PoseInterval
import Noperthedron.Nopert
import Noperthedron.SolutionTable

theorem exists_solution_table :
    ∃ (tab : Solution.Table) (tab_valid : tab.Valid)
      (hz : 0 < tab.size),
      tightInterval ⊆ tab[0].toPoseInterval
     := by
  sorry -- TODO(hard)
