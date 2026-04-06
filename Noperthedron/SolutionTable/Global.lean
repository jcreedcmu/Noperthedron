import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.SolutionTable.Basic
import Noperthedron.Nopert

namespace Solution

theorem valid_global_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  let iv := row.toPoseInterval
  let pbar := iv.center
  let ε := iv.radius
  have hε : 0 ≤ ε := by sorry
  rintro ⟨q, hqi, hqr⟩
  have hq := q ∈ pbar.closed_ball ε
  have := RationalApprox.GlobalTheorem.rational_global pbar ε hε
  sorry
