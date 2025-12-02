import Noperthedron.PoseInterval
import Noperthedron.Nopert
import Noperthedron.SolutionTable

theorem Solution.Row.valid_imp_not_rupert
   (tab : Solution.Table) (tab_valid : tab.Valid)
   (row : Solution.Row) (row_valid : row.Valid tab) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  match row_valid with
  | .asSplit y => sorry
  | .asGlobal y => sorry
  | .asLocal y=> sorry

theorem exists_solution_table :
    ∃ (tab : Solution.Table) (tab_valid : tab.Valid)
      (row : Solution.Row) (row_valid : row.Valid tab),
      tightInterval ⊆ row.toPoseInterval
     := by
  sorry -- TODO(hard)
