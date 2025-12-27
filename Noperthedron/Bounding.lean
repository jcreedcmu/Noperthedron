import Noperthedron.Basic
import Noperthedron.Lemma9
import Noperthedron.Lemma11
import Noperthedron.Lemma12

open scoped RealInnerProductSpace Real

namespace Bounding


theorem norm_sub_rotR_le (α β : ℝ) : ‖rotR α - rotR β‖ ≤ 2 * |Real.sin ((α - β) / 2)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [ContinuousLinearMap.sub_apply, ←sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow]
  nth_rw 1 [show α = (α + β) / 2 + (α - β) / 2 by ring]
  nth_rw 3 [show β = (α + β) / 2 - (α - β) / 2 by ring]
  simp only [rotR, rotR_mat, AddChar.coe_mk, Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub,
    LinearMap.coe_toContinuousLinearMap', EuclideanSpace.norm_sq_eq, PiLp.sub_apply, Matrix.cons_val,
    Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
    Matrix.vecHead, Matrix.vecTail, Matrix.dotProduct_of_isEmpty, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two]
  ring_nf
  simp only [one_div, Fin.isValue, sq_abs, Real.cos_sq']
  grind

theorem norm_rotR_sub_rotR_lt {ε α α_ : ℝ} (hε : 0 < ε) (hα : |α - α_| ≤ ε) :
    ‖rotR α - rotR α_‖ < ε := by
  wlog H : 0 ≤ α - α_
  · grind [abs_sub_comm, norm_sub_rev]
  apply lt_of_le_of_lt (norm_sub_rotR_le α α_)
  obtain h | rfl := lt_or_eq_of_le hα
  · grw [Real.abs_sin_le_abs]
    rw [abs_div, abs_two]
    linarith only [h]
  · have h := Real.abs_sin_lt_abs (div_ne_zero (abs_pos.mp hε) two_ne_zero)
    rw [abs_div, abs_two] at h
    linarith only [h]

theorem norm_RxL_sub_RxL_eq {α α_ : ℝ} : ‖RxL α - RxL α_‖ = ‖rotR α - rotR α_‖ := by
  simp only [Norm.norm, ContinuousLinearMap.opNorm]
  congr! 3 with x
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, RxL, Matrix.toEuclideanLin,
    Rx_mat, LinearEquiv.trans_apply, ContinuousLinearMap.coe_sub',
    LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, LinearEquiv.arrowCongr_apply,
    LinearEquiv.symm_symm, WithLp.linearEquiv_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, WithLp.addEquiv_apply, Matrix.toLin'_apply, Matrix.cons_mulVec,
    Matrix.cons_dotProduct, one_mul, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, neg_mul,
    zero_add, Matrix.empty_mulVec, WithLp.linearEquiv_symm_apply, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply, PiLp.sub_apply, ENNReal.toReal_ofNat,
    Real.rpow_ofNat, sq_abs, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, sub_self, ne_eq,
    not_false_eq_true, zero_pow, Matrix.cons_val_one, Matrix.cons_val, one_div, rotR, rotR_mat,
    AddChar.coe_mk, Fin.sum_univ_two, Matrix.cons_val_fin_one, and_congr_right_iff]
  intro hx
  apply Iff.intro
  · intro h₁ v
    simpa using h₁ !₂[0, v 0, v 1]
  · intro h₁ v
    specialize h₁ !₂[v 1, v 2]
    simp only [Matrix.vecHead, Fin.isValue, Matrix.cons_val_zero, Matrix.vecTail,
      Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h₁
    simp only [Matrix.vecHead, Matrix.vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring_nf at h₁ ⊢
    calc _ ≤ _ := h₁
         _ ≤ _ := by
           refine mul_le_mul_of_nonneg_left ?_ hx
           exact (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity))

theorem norm_RyL_sub_RyL_eq {α α_ : ℝ} : ‖RyL α - RyL α_‖ = ‖rotR α - rotR α_‖ := by
  simp only [Norm.norm, ContinuousLinearMap.opNorm]
  congr! 3 with x
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, RyL, Matrix.toEuclideanLin,
    Ry_mat, LinearEquiv.trans_apply, ContinuousLinearMap.coe_sub',
    LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, LinearEquiv.arrowCongr_apply,
    LinearEquiv.symm_symm, WithLp.linearEquiv_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, WithLp.addEquiv_apply, Matrix.toLin'_apply, Matrix.cons_mulVec,
    Matrix.cons_dotProduct, one_mul, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, neg_mul,
    zero_add, Matrix.empty_mulVec, WithLp.linearEquiv_symm_apply, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply, PiLp.sub_apply, ENNReal.toReal_ofNat,
    Real.rpow_ofNat, sq_abs, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, sub_self, ne_eq,
    not_false_eq_true, zero_pow, Matrix.cons_val_one, Matrix.cons_val, one_div, rotR, rotR_mat,
    AddChar.coe_mk, Fin.sum_univ_two, Matrix.cons_val_fin_one, and_congr_right_iff]
  intro hx
  apply Iff.intro
  · intro h₁ v
    simpa using h₁ !₂[v 0, 0, v 1]
  · intro h₁ v
    specialize h₁ !₂[v 0, v 2]
    simp only [Matrix.vecHead, Fin.isValue, Matrix.cons_val_zero, Matrix.vecTail,
      Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h₁
    simp only [Matrix.vecHead, Matrix.vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring_nf at h₁ ⊢
    calc _ ≤ _ := h₁
         _ ≤ _ := by
           refine mul_le_mul_of_nonneg_left ?_ hx
           exact (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity))

theorem norm_RzL_sub_RzL_eq {α α_ : ℝ} : ‖RzL α - RzL α_‖ = ‖rotR α - rotR α_‖ := by
  simp only [Norm.norm, ContinuousLinearMap.opNorm]
  congr! 3 with x
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, RzL, Matrix.toEuclideanLin,
    Rz_mat, LinearEquiv.trans_apply, ContinuousLinearMap.coe_sub',
    LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, LinearEquiv.arrowCongr_apply,
    LinearEquiv.symm_symm, WithLp.linearEquiv_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, WithLp.addEquiv_apply, Matrix.toLin'_apply, Matrix.cons_mulVec,
    Matrix.cons_dotProduct, one_mul, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, neg_mul,
    zero_add, Matrix.empty_mulVec, WithLp.linearEquiv_symm_apply, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply, PiLp.sub_apply, ENNReal.toReal_ofNat,
    Real.rpow_ofNat, sq_abs, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, sub_self, ne_eq,
    not_false_eq_true, zero_pow, Matrix.cons_val_one, Matrix.cons_val, one_div, rotR, rotR_mat,
    AddChar.coe_mk, Fin.sum_univ_two, Matrix.cons_val_fin_one, and_congr_right_iff]
  intro hx
  apply Iff.intro
  · intro h₁ v
    simpa using h₁ !₂[v 0, v 1, 0]
  · intro h₁ v
    specialize h₁ !₂[v 0, v 1]
    simp only [Matrix.vecHead, Fin.isValue, Matrix.cons_val_zero, Matrix.vecTail,
      Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h₁
    simp only [Matrix.vecHead, Matrix.vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Function.comp_apply, Fin.succ_zero_eq_one]
    ring_nf at h₁ ⊢
    calc _ ≤ _ := h₁
         _ ≤ _ := by
           refine mul_le_mul_of_nonneg_left ?_ hx
           exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)

theorem norm_RxRy_minus_id_le {α β : ℝ} : ‖RxL α ∘L RyL β - 1‖ ≤ √(α ^ 2 + β ^ 2) := by
  have := lemma12 (α := α) (β := β) zero_ne_one
  simp only [rot3] at this
  exact this

theorem reduceL_norm : ‖reduceL‖ = 1 := by
  have h₁ : reduceL = rotM 0 0 := by simp [rotM, reduceL, rotM_mat]
  rw [h₁]
  exact Bounding.rotM_norm_one 0 0

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
  sorry

theorem norm_X_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖vecX θ φ - vecX θ_ φ_‖ < √2 * ε := by
  by_cases h₁ : θ = θ_ ∧ φ = φ_
  · have h₂ : ‖vecX θ φ - vecX θ_ φ_‖ = 0 := by
      obtain ⟨hθ₁, hφ₁⟩ := h₁
      simp [hθ₁, hφ₁]
    rw [h₂]
    positivity
  sorry

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

theorem norm_RM_sub_RM_le {ε θ θ_ φ φ_ α α_}
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) (hα : |α - α_| ≤ ε) :
    ‖rotprojRM θ φ α - rotprojRM θ_ φ_ α_‖ < √5 * ε := by
  sorry
