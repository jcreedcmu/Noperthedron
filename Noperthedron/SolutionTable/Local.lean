import Noperthedron.SolutionTable.Basic
import Noperthedron.Local.Congruent
import Noperthedron.Vertices.Exact

namespace Noperthedron.Solution

theorem valid_local_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidLocal tab) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  sorry
