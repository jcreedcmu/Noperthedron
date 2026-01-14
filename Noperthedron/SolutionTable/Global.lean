import Noperthedron.SolutionTable.Basic
import Noperthedron.Nopert

namespace Solution

theorem valid_global_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  sorry
