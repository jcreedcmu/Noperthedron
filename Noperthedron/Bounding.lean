import Noperthedron.Basic
import Noperthedron.Bounding.Lemma11
import Noperthedron.Bounding.SmallConsecutiveRotations
import Noperthedron.Bounding.OpNorm

open scoped RealInnerProductSpace Real

namespace Bounding

lemma RyL_neg_compose_RyL {α : ℝ} : RyL (-α) ∘L RyL α = ContinuousLinearMap.id _ _ := by
  have h₄ : (RyL (-α)).comp (RyL α) = RyL (-α + α) := by
    rw [show RyL = RyC from rfl]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
  rw [h₄]
  rw [show RyL = RyC from rfl]
  simp [ContinuousLinearMap.one_def]

lemma RzL_neg_compose_RzL {α : ℝ} : RzL (-α) ∘L RzL α = ContinuousLinearMap.id _ _ := by
  have h₄ : (RzL (-α)).comp (RzL α) = RzL (-α + α) := by
    rw [show RzL = RzC from rfl]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
  rw [h₄]
  rw [show RzL = RzC from rfl]
  simp [ContinuousLinearMap.one_def]

/--
First half of Lemma 13 from [SY25].
-/
theorem norm_M_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖rotM θ φ - rotM θ_ φ_‖ < √2 * ε := by
  by_cases h₁ : θ = θ_ ∧ φ = φ_
  · have h₂ : ‖rotM θ φ - rotM θ_ φ_‖ = 0 := by
      obtain ⟨hθ₁, hφ₁⟩ := h₁
      simp [hθ₁, hφ₁]
    rw [h₂]
    positivity
  simp only [rotM_identity, ←ContinuousLinearMap.comp_sub]
  grw [ContinuousLinearMap.opNorm_comp_le, reduceL_norm, one_mul]
  rw [←Ry_preserves_op_norm (-φ), ContinuousLinearMap.comp_sub]
  rw [←Rz_comp_right_preserves_op_norm θ, ContinuousLinearMap.sub_comp]
  have h₂ : ((RyL (-φ)).comp ((RyL φ).comp (RzL (-θ)))).comp (RzL θ) =
      (RyL (-φ) ∘L (RyL φ)) ∘L (RzL (-θ) ∘L (RzL θ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₂, RyL_neg_compose_RyL, RzL_neg_compose_RzL, ContinuousLinearMap.id_comp,
      ←ContinuousLinearMap.one_def]
  have h₆ : ((RyL (-φ)).comp ((RyL φ_).comp (RzL (-θ_)))).comp (RzL θ) =
      (RyL (-φ) ∘L (RyL φ_)) ∘L (RzL (-θ_) ∘L (RzL θ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₆]
  clear h₂ h₆
  rw [show RyL = RyC from rfl, show RzL = RzC from rfl]
  rw [show (RzC (-θ_)).comp (RzC θ) = (RzC (-θ_)) * (RzC θ) from rfl]
  rw [show (RyC (-φ)).comp (RyC φ_) = (RyC (-φ)) * (RyC φ_) from rfl]
  simp only [←AddChar.map_add_eq_mul]
  rw [norm_sub_rev]
  have h₇ := lemma12 (d := 1) (d' := 2) (α := -φ + φ_) (β := -θ_ + θ) (by decide)
  have h₇' := lemma12_equality_iff (d := 1) (d' := 2) (α := -φ + φ_) (β := -θ_ + θ) (by decide)
  have h11 : ¬ (-φ + φ_ = 0 ∧ -θ_ + θ = 0) := by grind
  replace h₇' := h₇'.not.mpr h11
  replace h₇ := lt_of_le_of_ne h₇ h₇'
  simp only [rot3] at h₇
  suffices √((-φ + φ_) ^ 2 + (-θ_ + θ) ^ 2) ≤ √2 * ε by linarith
  rw [←sq_abs (-φ + _), ←sq_abs (-θ_ + _)]
  suffices (√(|-φ + φ_| ^ 2 + |-θ_ + θ| ^ 2)) ^ 2 ≤ (√2 * ε) ^ 2 by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp this
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), two_mul]
  rw [show |-θ_ + θ| = |θ - θ_| by grind, show |-φ + φ_| = |φ - φ_| by grind]
  gcongr

/--
Second half of Lemma 13 from [SY25].
-/
theorem norm_X_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖vecX θ φ - vecX θ_ φ_‖ < √2 * ε := by
  by_cases h₁ : θ = θ_ ∧ φ = φ_
  · have h₂ : ‖vecX θ φ - vecX θ_ φ_‖ = 0 := by
      obtain ⟨hθ₁, hφ₁⟩ := h₁
      simp [hθ₁, hφ₁]
    rw [h₂]
    positivity
  simp only [vecX_identity, ←ContinuousLinearMap.sub_apply]
  grw [ContinuousLinearMap.le_opNorm]
  have h₉₉ : ‖!₂[0, 0, (1:ℝ)]‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [h₉₉, mul_one]; clear h₉₉
  rw [←Rz_preserves_op_norm (-θ), ContinuousLinearMap.comp_sub]
  rw [←Ry_comp_right_preserves_op_norm φ, ContinuousLinearMap.sub_comp]
  have h₂ : ((RzL (-θ)).comp ((RzL θ).comp (RyL (-φ)))).comp (RyL φ) =
      (RzL (-θ) ∘L (RzL θ)) ∘L (RyL (-φ) ∘L (RyL φ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₂, RyL_neg_compose_RyL, RzL_neg_compose_RzL, ContinuousLinearMap.id_comp,
      ←ContinuousLinearMap.one_def]
  have h₆ : ((RzL (-θ)).comp ((RzL θ_).comp (RyL (-φ_)))).comp (RyL φ) =
      (RzL (-θ) ∘L (RzL θ_)) ∘L (RyL (-φ_) ∘L (RyL φ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₆]
  clear h₂ h₆
  rw [show RyL = RyC from rfl, show RzL = RzC from rfl]
  rw [show (RyC (-φ_)).comp (RyC φ) = (RyC (-φ_)) * (RyC φ) from rfl]
  rw [show (RzC (-θ)).comp (RzC θ_) = (RzC (-θ)) * (RzC θ_) from rfl]
  simp only [←AddChar.map_add_eq_mul]
  rw [norm_sub_rev]
  have h₇ := lemma12 (d := 2) (d' := 1) (α := -θ + θ_) (β := -φ_ + φ) (by decide)
  have h₇' := lemma12_equality_iff (d := 2) (d' := 1) (α := -θ + θ_) (β := -φ_ + φ) (by decide)
  have h11 : ¬ (-θ + θ_ = 0 ∧ -φ_ + φ = 0) := by grind
  replace h₇' := h₇'.not.mpr h11
  replace h₇ := lt_of_le_of_ne h₇ h₇'
  simp only [rot3] at h₇
  suffices √((-θ + θ_) ^ 2 + (-φ_ + φ) ^ 2) ≤ √2 * ε by linarith
  rw [←sq_abs (-θ + _), ←sq_abs (-φ_ + _)]
  suffices (√(|-θ + θ_| ^ 2 + |-φ_ + φ| ^ 2)) ^ 2 ≤ (√2 * ε) ^ 2 by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp this
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), two_mul]
  rw [show |-φ_ + φ| = |φ - φ_| by grind, show |-θ + θ_| = |θ - θ_| by grind]
  gcongr

/--
[SY25] Lemma 14
-/
theorem XPgt0 {P : ℝ³} {ε θ θ_ φ φ_ : ℝ} (hP : ‖P‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hX : √2 * ε < ⟪vecX θ_ φ_, P⟫) :
    0 < ⟪vecX θ φ, P⟫ := by
  have h₁ : ‖⟪vecX θ_ φ_ - vecX θ φ, P⟫‖ ≤ ‖vecX θ_ φ_ - vecX θ φ‖ * ‖P‖ := by
    exact norm_inner_le_norm (vecX θ_ φ_ - vecX θ φ) P
  grw [inner_sub_left, ←Real.le_norm_self] at h₁
  rw [tsub_le_iff_tsub_le] at h₁
  have h₂ := norm_X_sub_lt hε hθ hφ
  grw [← h₁]
  rw [norm_sub_rev] at h₂
  have h₃ : ‖vecX θ_ φ_ - vecX θ φ‖ * ‖P‖ ≤ ‖vecX θ_ φ_ - vecX θ φ‖ * 1 :=
     mul_le_mul_of_nonneg_left hP (norm_nonneg _)
  linarith

/--
[SY25] Lemma 15
-/
theorem norm_M_apply_gt {ε r θ θ_ φ φ_ : ℝ} {P : ℝ³}
    (hP : ‖P‖ ≤ 1) (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hM : r + √2 * ε < ‖rotM θ_ φ_ P‖) : r < ‖rotM θ φ P‖ := by
  have h₁ : ‖rotM θ_ φ_ P‖ - ‖rotM θ φ - rotM θ_ φ_‖ * ‖P‖ ≤ ‖rotM θ φ P‖ := by
    grw [←ContinuousLinearMap.le_opNorm, ContinuousLinearMap.sub_apply]
    suffices ‖(rotM θ_ φ_) P‖ ≤ ‖(rotM θ φ) P‖ + ‖(rotM θ φ) P - (rotM θ_ φ_) P‖ by linarith
    exact norm_le_insert ((rotM θ φ) P) ((rotM θ_ φ_) P)
  have h₂ := norm_M_sub_lt hε hθ hφ
  grw [hP, mul_one] at h₁
  linarith

/--
[SY25] Lemma 16
-/
theorem norm_RM_sub_RM_le {ε θ θ_ φ φ_ α α_}
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) (hα : |α - α_| ≤ ε) :
    ‖rotprojRM θ φ α - rotprojRM θ_ φ_ α_‖ < √5 * ε := by
  simp only [rotprojRM_identity, ←ContinuousLinearMap.comp_sub]
  grw [ContinuousLinearMap.opNorm_comp_le, reduceL_norm, one_mul]
  rw [←Rz_preserves_op_norm (-α_), ContinuousLinearMap.comp_sub]
  rw [←Rz_comp_right_preserves_op_norm θ, ContinuousLinearMap.sub_comp]
  have h₃ : ((RzL (-α_)).comp ((RzL α).comp ((RyL φ).comp (RzL (-θ))))).comp (RzL θ) =
      RzL (-α_) ∘L RzL α ∘L RyL φ ∘L RzL (-θ) ∘L RzL θ := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc]
  have h₄ : ((RzL (-α_)).comp ((RzL α_).comp ((RyL φ_).comp (RzL (-θ_))))).comp (RzL θ) =
        (RzL (-α_) ∘L RzL α_) ∘L RyL φ_ ∘L RzL (-θ_) ∘L RzL θ
       := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₃, h₄, RzL_neg_compose_RzL, RzL_neg_compose_RzL]
  clear h₃ h₄
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  let Φ := (φ * |θ - θ_| + φ_ * |α - α_|) / (|α - α_| + |θ - θ_|)
  have h₅ : ((RzL (-θ_)).comp (RzL θ)) = RzL (θ - θ_) := by
    rw [show RzL = RzC from rfl]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
    rw [show -θ_ + θ = θ - θ_ by ring]
  rw [h₅]; clear h₅
  rw [←ContinuousLinearMap.comp_assoc]
  have h₅ : ((RzL (-α_)).comp (RzL α)) = RzL (α - α_) := by
    rw [show RzL = RzC from rfl]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
    ring_nf
  rw [h₅]; clear h₅
  have h₆ :
      ‖(RzL (α - α_)).comp (RyL φ) - RyL Φ‖ + ‖ RyL Φ - (RyL φ_).comp (RzL (θ - θ_))‖
      ≥ ‖(RzL (α - α_)).comp (RyL φ) - (RyL φ_).comp (RzL (θ - θ_))‖ := by
    have :=
      ContinuousLinearMap.opNorm_add_le ((RzL (α - α_)).comp (RyL φ) - RyL Φ)
        (RyL Φ - (RyL φ_).comp (RzL (θ - θ_)))
    rwa [sub_add_sub_cancel] at this
  grw [←h₆]; clear h₆
  nth_rw 1 [←Ry_comp_right_preserves_op_norm (-Φ)]
  nth_rw 2 [←Ry_preserves_op_norm (-Φ)]
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, RyL_neg_compose_RyL]
  have h₇ := RyL_neg_compose_RyL (α := -Φ)
  rw [neg_neg] at h₇
  rw [h₇]
  sorry
