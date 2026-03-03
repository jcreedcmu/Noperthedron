import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Congruence
import Noperthedron.SolutionTable.RationalLocalCheck
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
    (p_ : Pose) (ε δ r : ℝ)
    (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt)
    (pc : RationalApprox.LocalTheorem.RationalLocalTheoremPrecondition
      Nopert.poly poly_ hpoly (Row.PTriangle row) (Row.QTriangle row) p_ ε δ r su sl) :
    ¬∃ p ∈ p_.closed_ball ε, RupertPose p Nopert.poly.hull := by
  have hcong : (Row.PTriangle row).Congruent (Row.QTriangle row) :=
    valid_local_imp_congruent tab row hr
  exact RationalApprox.LocalTheorem.rational_local_of_precondition
    Nopert.poly poly_ hpoly (Row.PTriangle row) (Row.QTriangle row) p_ ε δ r su sl hcong pc

theorem valid_local_imp_no_rupert_rational_from_row (tab : Table) (row : Row)
    (hr : row.ValidLocal tab)
    (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt)
    (hpre : row.localPreconditionCheck su sl) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q Nopert.poly.hull := by
  have hcong : (Row.PTriangle row).Congruent (Row.QTriangle row) :=
    valid_local_imp_congruent tab row hr
  have hpc := Row.localPreconditionCheck_to_precondition row su sl hpre
  have hno :=
    RationalApprox.LocalTheorem.rational_local_of_precondition
      Nopert.poly Nopert.poly (RationalApprox.κApproxPoly.refl Nopert.poly)
      (Row.PTriangle row) (Row.QTriangle row)
      row.localPose row.localEps (row.localDelta su) (row.localR) su sl hcong hpc
  intro hrupert
  rcases hrupert with ⟨q, hq, hru⟩
  exact hno ⟨q, mem_poseInterval_imp_mem_closed_ball row q hq, hru⟩

theorem valid_local_imp_no_rupert_rational_from_row_bool (tab : Table) (row : Row)
    (hr : row.ValidLocal tab)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (alg : Solution.LocalPrecheckAlg su sl)
    (hpre : row.localPreconditionCheckBool alg = true) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q Nopert.poly.hull := by
  have hspec : row.localPreconditionCheck su sl :=
    Solution.localPreconditionCheckBool_sound row alg hpre
  exact valid_local_imp_no_rupert_rational_from_row tab row hr su sl hspec

theorem valid_local_imp_no_rupert_rational_from_cert (tab : Table) (row : Row)
    (hr : row.ValidLocal tab)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (cert : Solution.LocalPrecheckCertificate tab su sl)
    (hpre :
      row.localPreconditionCheckBool
        (Solution.LocalPrecheckAlg.ofOracle (Solution.LocalPrecheckCertificate.toOracle cert)) = true) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q Nopert.poly.hull := by
  exact valid_local_imp_no_rupert_rational_from_row_bool tab row hr
    (Solution.LocalPrecheckAlg.ofOracle (Solution.LocalPrecheckCertificate.toOracle cert)) hpre
