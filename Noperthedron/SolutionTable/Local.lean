import Noperthedron.SolutionTable.Basic
import Noperthedron.Nopert
import Noperthedron.Local.Congruent

namespace Solution

theorem valid_local_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidLocal tab) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  sorry
