import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.RationalGlobalCheck
import Noperthedron.Nopert
import Noperthedron.RationalApprox.RationalGlobal

namespace Solution

theorem valid_global_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  exact hr.no_rupert

theorem valid_global_imp_no_rupert_rational_from_row (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab)
    (S : ℝ³) (hpre : row.globalPreconditionCheck S) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  have hpc := Row.globalPreconditionCheck_to_precondition row S hpre
  have hε : 0 < row.globalEps := hpre.2.2.1
  have hsym : PointSym nopert.hull := nopert_point_symmetric
  have hno :=
    RationalApprox.GlobalTheorem.rational_global
      row.globalPose row.globalEps hε
      Nopert.poly Nopert.poly.toApproxGoodPoly (RationalApprox.κApproxPoly.refl Nopert.poly)
      hsym hpc
  intro hrupert
  rcases hrupert with ⟨q, hq, hru⟩
  have hmem : q ∈ row.globalPose.closed_ball row.globalEps :=
    mem_poseInterval_imp_mem_closed_ball row q hq
  exact hno ⟨q, hmem, hru⟩

theorem valid_global_imp_no_rupert_rational_from_row_bool (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab)
    (alg : GlobalPrecheckAlg)
    (hpre : row.globalPreconditionCheckBool alg = true) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  have hspec : row.globalPreconditionCheck (alg.S row) :=
    globalPreconditionCheckBool_sound row alg hpre
  exact valid_global_imp_no_rupert_rational_from_row tab row hr (alg.S row) hspec

theorem valid_global_imp_no_rupert_rational_from_cert (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab)
    (cert : GlobalPrecheckCertificate tab)
    (hpre : row.globalPreconditionCheckBool (GlobalPrecheckCertificate.toAlg cert) = true) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  exact valid_global_imp_no_rupert_rational_from_row_bool tab row hr
    (GlobalPrecheckCertificate.toAlg cert) hpre
