import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Congruence
import Noperthedron.SolutionTable.RationalLocalCheck
import Noperthedron.SolutionTable.RationalGlobalCheck
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.RationalApprox.RationalLocal
import Noperthedron.Nopert

namespace Solution

open scoped Real

lemma nopert_poly_hull_eq_nopert_hull : Nopert.poly.hull = nopert.hull := by
  simp [GoodPoly.hull, Shape.hull, Nopert.poly, nopert]

lemma nopert_poly_pointsym : PointSym Nopert.poly.hull := by
  simpa [nopert_poly_hull_eq_nopert_hull] using nopert_point_symmetric

structure Row.ValidGlobalRational (tab : Table) (row : Row) : Type where
  nodeType : row.nodeType = 1
  eps_pos : 0 < row.localEps
  pre :
    RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
      Nopert.poly Nopert.poly.toApproxGoodPoly (RationalApprox.κApproxPoly.refl Nopert.poly)
      row.localPose row.localEps

structure Row.ValidLocalRational (tab : Table) (row : Row) : Type where
  congruence_check : row.localCongruenceIndexCheck
  su : RationalApprox.UpperSqrt
  sl : RationalApprox.LowerSqrt
  precheck : row.localPreconditionCheck su sl

noncomputable def Row.ValidGlobalRational.ofPrecheckBool (tab : Table) (row : Row)
    (alg : Solution.GlobalPrecheckAlg)
    (hpre : row.globalPreconditionCheckBool alg = true) :
    Row.ValidGlobalRational tab row := by
  have hspec : row.globalPreconditionCheck (alg.S row) :=
    Solution.globalPreconditionCheckBool_sound row alg hpre
  rcases hspec with ⟨hnode, hp4, hε, hw, hS, hEx⟩
  refine {
    nodeType := hnode
    eps_pos := hε
    pre := ?_
  }
  exact Row.globalPreconditionCheck_to_precondition row (alg.S row)
    ⟨hnode, hp4, hε, hw, hS, hEx⟩

noncomputable def Row.ValidLocalRational.ofPrecheckBool (tab : Table) (row : Row)
    (hc : row.localCongruenceIndexCheck)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (alg : Solution.LocalPrecheckAlg su sl)
    (hpre : row.localPreconditionCheckBool alg = true) :
    Row.ValidLocalRational tab row := by
  have hspec : row.localPreconditionCheck su sl :=
    Solution.localPreconditionCheckBool_sound row alg hpre
  exact {
    congruence_check := hc
    su := su
    sl := sl
    precheck := hspec
  }

lemma no_rupert_of_subset {A B : PoseInterval}
    (hAB : A ⊆ B)
    (hB : ¬ ∃ q ∈ B, RupertPose q nopert.hull) :
    ¬ ∃ q ∈ A, RupertPose q nopert.hull := by
  rintro ⟨q, hqA, hqR⟩
  exact hB ⟨q, hAB q hqA, hqR⟩

lemma Row.ValidGlobalRational.toValidGlobal (tab : Table) (row : Row)
    (h : Row.ValidGlobalRational tab row) : Row.ValidGlobal tab row := by
  refine ⟨h.nodeType, ?_⟩
  have hball :
      ¬ ∃ p ∈ row.localPose.closed_ball row.localEps, RupertPose p nopert.hull := by
    -- Apply the rational global theorem at the midpoint pose.
    have h' :
        ¬ ∃ p ∈ row.localPose.closed_ball row.localEps, RupertPose p Nopert.poly.hull := by
      simpa using
        (RationalApprox.GlobalTheorem.rational_global row.localPose row.localEps h.eps_pos
          Nopert.poly Nopert.poly.toApproxGoodPoly (RationalApprox.κApproxPoly.refl Nopert.poly)
          nopert_poly_pointsym h.pre)
    simpa [nopert_poly_hull_eq_nopert_hull] using h'
  -- Restrict from the closed ball to the row's pose interval.
  have hsub : row.toPoseInterval ⊆ row.localPose.closed_ball row.localEps := by
    intro q hq
    exact mem_poseInterval_imp_mem_closed_ball row q hq
  exact no_rupert_of_subset hsub hball

lemma Row.ValidLocalRational.toValidLocal (tab : Table) (row : Row)
    (h : Row.ValidLocalRational tab row) : Row.ValidLocal tab row := by
  classical
  -- Extract the local row precondition and build the packaged precondition type.
  have hc : row.localCongruenceIndexCheck := h.congruence_check
  have pc := Row.localPreconditionCheck_to_precondition row h.su h.sl h.precheck
  have hcong : (Row.PTriangle row).Congruent (Row.QTriangle row) :=
    localCongruenceIndexCheck_sound row hc
  have hball :
      ¬ ∃ p ∈ row.localPose.closed_ball row.localEps, RupertPose p nopert.hull := by
    have h' :
        ¬ ∃ p ∈ row.localPose.closed_ball row.localEps, RupertPose p Nopert.poly.hull :=
      RationalApprox.LocalTheorem.rational_local_of_precondition
        Nopert.poly Nopert.poly (RationalApprox.κApproxPoly.refl Nopert.poly)
        (Row.PTriangle row) (Row.QTriangle row) row.localPose row.localEps
        (row.localDelta h.su) (row.localR) h.su h.sl hcong pc
    simpa [nopert_poly_hull_eq_nopert_hull] using h'
  have hsub : row.toPoseInterval ⊆ row.localPose.closed_ball row.localEps := by
    intro q hq
    exact mem_poseInterval_imp_mem_closed_ball row q hq
  have hnorow : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull :=
    no_rupert_of_subset hsub hball
  -- Package into the existing `Row.ValidLocal` structure.
  refine ⟨?_, hc, hnorow⟩
  -- The node type fact is part of `localPreconditionCheck`.
  exact h.precheck.1

end Solution
