import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Congruence
import Noperthedron.Nopert
import Noperthedron.Local.Congruent
import Noperthedron.RationalApprox.RationalLocal

namespace Solution

theorem valid_local_imp_congruent (tab : Table) (row : Row)
    (hr : row.ValidLocal tab) :
    (Row.PTriangle row).Congruent (Row.QTriangle row) :=
  validLocal_congruent tab row hr

theorem valid_local_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidLocal tab) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  exact hr.no_rupert

theorem valid_local_imp_no_rupert_rational (tab : Table) (row : Row)
    (hr : row.ValidLocal tab)
    (poly_ : GoodPoly)
    (hpoly : RationalApprox.κApproxPoly Nopert.poly.vertices poly_.vertices)
    (p_ : Pose) (ε δ r : ℝ) (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt)
    (pc : RationalApprox.LocalTheorem.RationalLocalTheoremPrecondition
      Nopert.poly poly_ hpoly (Row.PTriangle row) (Row.QTriangle row) p_ ε δ r su sl) :
    ¬∃ p ∈ p_.closed_ball ε, RupertPose p Nopert.poly.hull := by
  have hcong : (Row.PTriangle row).Congruent (Row.QTriangle row) :=
    valid_local_imp_congruent tab row hr
  exact RationalApprox.LocalTheorem.rational_local_of_precondition
    Nopert.poly poly_ hpoly (Row.PTriangle row) (Row.QTriangle row) p_ ε δ r su sl hcong pc
