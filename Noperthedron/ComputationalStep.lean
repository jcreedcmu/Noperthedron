import Noperthedron.PoseInterval
import Noperthedron.Nopert
import Noperthedron.SolutionTable

theorem Row.valid_imp_not_rupert (tab : Solution.Table)
   (row : Solution.Row) (row_valid : row.Valid tab) :
    ¬ ∃ q ∈ row.toPoseInterval, Shadows.IsRupert q nopert.hull := by
  match row_valid with
  | .asSplit y => sorry
  | .asGlobal y => sorry
  | .asLocal y=> sorry
