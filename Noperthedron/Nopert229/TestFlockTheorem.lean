import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open scoped BigOperators RealInnerProductSpace
open Noperthedron.Nopert229
open Noperthedron.SnubCube
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveLocalCertificate
open AtlasProjectiveView

namespace Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

theorem valid_imp_not_translated_rupert_of_flock_decomposed
    (box : Box)
    (M : ℕ)
    (coreAxes : Fin M → AxisCertificate)
    (defect0 : Fin 3 → ℚ) (D0 : ℚ)
    (r_min : ℚ) (c_cone : ℚ) (c_core : ℚ)
    (hr_min_nonneg : 0 ≤ r_min)
    (hr_nonneg : 0 ≤ box.r)
    (hr_le_two : box.r ≤ 2)
    (hmismatch : box.mismatchRadius ≤ box.r)
    (hdelta_nonneg : 0 ≤ box.δ)
    (hc_nonneg : 0 ≤ box.c)
    (hbary : box.decomposedBarycentricValid c_cone)
    (hD0_nonneg : 0 ≤ D0)
    (hdefect0_nonneg : ∀ i, 0 ≤ defect0 i)
    (hdefect_budget0 : (∑ i, box.weightUpper 0 i * defect0 i) ≤ D0)
    (hc_cone_margin : box.δ ≤ c_cone)
    (hannular_dominance :
      ((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤
        r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) *
          ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2))
    (hB_pos : ∀ j, 0 < (box.certificate j).B)
    (hvar : ∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
    (hsupp : ∀ j i k, box.supportUpper j i k ≤ if j = 0 then defect0 i else 0)
    (hdir_nonzero : ∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
    (hbudget : ∀ j, box.weightBudget j ≤ (box.certificate j).B)
    (hweight_nonneg : ∀ j i, 0 ≤ box.weightLower j i)
    (hweight_pos : ∀ j, ∃ i, 0 < box.weightLower j i)
    (hcomp_angle : box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2)
    (hc_core_margin : box.δ ≤ c_core)
    (hcore_B_pos : ∀ m, 0 < (coreAxes m).B)
    (hcore_var : ∀ m,
      (box.withCoreAxis (coreAxes m) c_core r_min).variationRadiusSum 0 + 3 * variationError ≤
        (coreAxes m).B * box.δ)
    (hcore_supp : ∀ m i k,
      (box.withCoreAxis (coreAxes m) c_core r_min).supportUpper 0 i k ≤ 0)
    (hcore_dir : ∀ m i,
      (box.withCoreAxis (coreAxes m) c_core r_min).supportUpper 0 i ((coreAxes m).nonzeroWitness i) < 0)
    (hcore_budget : ∀ m,
      (box.withCoreAxis (coreAxes m) c_core r_min).weightBudget 0 ≤ (coreAxes m).B)
    (hcore_weight_nonneg : ∀ m i,
      0 ≤ (box.withCoreAxis (coreAxes m) c_core r_min).weightLower 0 i)
    (hcore_weight_pos : ∀ m,
      ∃ i, 0 < (box.withCoreAxis (coreAxes m) c_core r_min).weightLower 0 i)
    (hcore_angle : r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2)
    (hexc_covers : ∀ axis, ‖axis‖ = 1 → (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0)) →
      ∃ m : Fin M, (c_core : ℝ) ≤ inner ℝ axis (toR3 ((box.withCoreAxis (coreAxes m) c_core r_min).approxNormalizedCenter 0)))
    (hc_cone_pos : 0 < c_cone)
    (hc_margin : box.δ ≤ box.c)
    (hc_sum_pos : 0 < box.c + box.δ)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  let exceptional : ℝ³ → Prop := fun axis =>
    (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0))
  apply valid_imp_not_translated_rupert_of_three_way_split box r_min exceptional
  · intro p' hp' off' hs' hm' a hnorm_lower hexc
    let fullDefect : Fin 4 → Fin 3 → ℚ := fun j =>
      if j = 0 then defect0 else fun _ => 0
    let fullD : Fin 4 → ℚ := fun j =>
      if j = 0 then D0 else 0
    have hD_nonneg : ∀ j, 0 ≤ fullD j := by
      intro j; dsimp [fullD]; split_ifs; exact hD0_nonneg; exact le_refl 0
    have hdefect_nonneg : ∀ j i, 0 ≤ fullDefect j i := by
      intro j i; dsimp [fullDefect]; split_ifs; exact hdefect0_nonneg i; exact le_refl 0
    have hsupp' : ∀ j i k, box.supportUpper j i k ≤ fullDefect j i := by
      intro j i k; have hs := hsupp j i k; dsimp [fullDefect]
      by_cases hj : j = 0
      · subst hj; simpa using hs
      · simpa [hj] using hs
    have hdefect_budget' : ∀ j, (∑ i, box.weightUpper j i * fullDefect j i) ≤ fullD j := by
      intro j; dsimp [fullD, fullDefect]; split_ifs with hj
      · subst hj; exact hdefect_budget0
      · simp
    apply not_rupertPose_of_annular_exceptional_cone_certificate box 0
      fullDefect fullD r_min hr_min_nonneg hr_nonneg hr_le_two
      hB_pos hdelta_nonneg hD_nonneg hdefect_nonneg hvar hsupp' hdir_nonzero
      hbudget hdefect_budget' hweight_nonneg hweight_pos c_cone hc_cone_margin
      exceptional (fun _ => Iff.rfl) hmismatch hannular_dominance hp' off' hs' hm' a
      hnorm_lower hexc
  · intro p' hp' off' hs' hm' a hnot_exc
    have ha_norm : ‖a.signedAxis‖ = 1 := a.signedAxis_norm
    obtain ⟨j, hj_cover⟩ := box.valid_decomposed_center_axis_cover_of_bounds c_cone
      hc_nonneg hdelta_nonneg hbary a.signedAxis ha_norm
    have hdelta_real : (0 : ℝ) ≤ (box.δ : ℝ) := by exact_mod_cast hdelta_nonneg
    have hj_ne_zero : j ≠ 0 := by
      intro hj0
      subst hj0
      apply decomposed_axis_cover_zero a.signedAxis c_cone box.c box.δ (box.approxNormalizedCenter 0)
        hc_cone_pos hc_sum_pos hj_cover hnot_exc
    have hj_supp : ∀ i k, box.supportUpper j i k ≤ 0 := by
      intro i k
      have hs := hsupp j i k
      split_ifs at hs with hj0
      · exact False.elim (hj_ne_zero hj0)
      · exact hs
    have hj_center : toR3 (box.decomposedCenter c_cone j) = toR3 (box.approxNormalizedCenter j) := by
      dsimp [Box.decomposedCenter]
      split_ifs with hj0
      · exact False.elim (hj_ne_zero hj0)
      · rfl
    have hj_cover' : (box.c : ℝ) ≤ inner ℝ a.signedAxis (toR3 (box.approxNormalizedCenter j)) := by
      rw [← hj_center]
      push_cast at hj_cover
      linarith
    apply not_rupertPose_of_single_complement_axis box j box.c
      hc_margin
      hB_pos hdelta_nonneg hr_nonneg hmismatch hvar hj_supp hdir_nonzero
      hbudget hweight_nonneg hweight_pos hcomp_angle hp' off' hs' hm' a hj_cover'
  · intro p' hp' off' hs' hm' a hnorm_upper hexc
    obtain ⟨m, hexc_core⟩ := hexc_covers a.signedAxis a.signedAxis_norm hexc
    let coreBox := box.withCoreAxis (coreAxes m) c_core r_min
    change ¬ RupertPose (p'.matrixPoseWithOffset coreBox.chart off') exactPolyhedron.hull
    let exc_single : ℝ³ → Prop := fun axis => axis = a.signedAxis
    apply not_rupertPose_of_inner_core_cone_axis coreBox r_min c_core exc_single
      hr_min_nonneg hc_core_margin (fun _ => hcore_B_pos m) hdelta_nonneg
      (fun _ => hcore_var m) (fun _ i k => hcore_supp m i k) (fun _ i => hcore_dir m i)
      (fun _ => hcore_budget m) (fun _ i => hcore_weight_nonneg m i) (fun _ => hcore_weight_pos m)
      (by intro ax ha he; subst he; exact hexc_core)
      hcore_angle hp' off' hs' hm' a hnorm_upper rfl
  · exact hp
  · exact hscale
  · exact hmem

end Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
