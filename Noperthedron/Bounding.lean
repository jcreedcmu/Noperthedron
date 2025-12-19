import Noperthedron.Basic
import Noperthedron.Lemma11

open scoped RealInnerProductSpace Real

namespace Bounding

theorem pres_norm_imp_norm_one {n m : ℕ} [NeZero n] {f : E n →L[ℝ] E m} (hf : (v : E n) → ‖f v‖ = ‖v‖) :
    ‖f‖ = 1 := by
  have decrease (x : E n) : ‖f x‖ ≤ 1 * ‖x‖ := by rw [hf x]; simp
  have increase (N : ℝ) (hN : N ≥ 0) (k : ∀ (x : E n), ‖f x‖ ≤ N * ‖x‖) : 1 ≤ N := by
    let e : E n := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have z := k e; rw [hf, he, mul_one] at z; exact z
  exact ContinuousLinearMap.opNorm_eq_of_bounds (by norm_num) decrease increase

theorem pres_sq_norm_imp_norm_one {n m : ℕ} [NeZero n] {f : E n →L[ℝ] E m}
    (hf : (v : E n) → ‖f v‖^2 = ‖v‖^2) : ‖f‖ = 1 := by
  refine pres_norm_imp_norm_one ?_
  intro v
  suffices h : ‖f v‖^2 = ‖v‖^2 by simp_all
  exact hf v

theorem rotR_norm_one (α : ℝ) : ‖rotR α‖ = 1 := by
  refine pres_sq_norm_imp_norm_one ?_
  intro v
  simp only [rotR, rotR_mat, PiLp.norm_sq_eq_of_L2]
  simp only [AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap', Matrix.piLp_ofLp_toEuclideanLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.vec2_dotProduct, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, neg_mul]
  ring_nf
  convert_to (v 0)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2) + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2) = _
  · ring_nf
  simp

theorem Rx_norm_one (α : ℝ) : ‖RxL α‖ = 1 := by
  refine pres_sq_norm_imp_norm_one ?_
  intro v
  simp only [RxL, Rx_mat, PiLp.norm_sq_eq_of_L2]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.piLp_ofLp_toEuclideanLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec3_dotProduct,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Matrix.cons_val]
  ring_nf
  convert_to (v 0)^2
           + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 2)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           = _
  · ring_nf
  simp

theorem Ry_norm_one (α : ℝ) : ‖RyL α‖ = 1 := by
  refine pres_sq_norm_imp_norm_one ?_
  intro v
  simp only [RyL, Ry_mat, PiLp.norm_sq_eq_of_L2]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.piLp_ofLp_toEuclideanLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec3_dotProduct,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Matrix.cons_val]
  ring_nf
  convert_to (v 0)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 1)^2
           + (v 2)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           = _
  · ring_nf
  simp only [Fin.isValue, Real.cos_sq_add_sin_sq, mul_one]

theorem Rz_pres_norm (α : ℝ) :
    ∀ (v : E 3), ‖(RzL α) v‖ = ‖v‖ := by
  intro v
  suffices h : ‖(RzL α) v‖^2 = ‖v‖^2  by simp_all
  simp only [RzL, Rz_mat, PiLp.norm_sq_eq_of_L2, AddChar.coe_mk]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.piLp_ofLp_toEuclideanLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec3_dotProduct,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Matrix.cons_val]
  ring_nf
  convert_to (v 0)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 2)^2
           = _
  · ring_nf
  simp only [Fin.isValue, Real.cos_sq_add_sin_sq, mul_one]

theorem Rz_norm_one (α : ℝ) : ‖RzL α‖ = 1 :=
  pres_norm_imp_norm_one (Rz_pres_norm α)

theorem rotM_norm_one (θ φ : ℝ) : ‖rotM θ φ‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    have h_expand :
        (-Real.sin θ * v 0 + Real.cos θ * v 1) ^ 2 +
         (-Real.cos θ * Real.cos φ * v 0 - Real.sin θ * Real.cos φ * v 1 + Real.sin φ * v 2) ^ 2 ≤
        v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
      have h₁ := sq_nonneg (Real.sin θ * v 1 + Real.cos θ * v 0)
      have h₂ := sq_nonneg (Real.sin θ * v 1 + Real.cos θ * v 0)
      have h₃ := sq_nonneg (Real.sin φ * (Real.cos θ * v 0 + Real.sin θ * v 1) + Real.cos φ * v 2)
      have h₄ := Real.sin_sq_add_cos_sq θ
      have h₅ := Real.sin_sq_add_cos_sq φ
      nlinarith
    simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.isValue,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, one_mul]
    convert Real.sqrt_le_sqrt h_expand using 1
    · simp only [rotM, Matrix.toEuclideanLin, rotM_mat, neg_mul, LinearEquiv.trans_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm,
        WithLp.linearEquiv_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
        WithLp.addEquiv_apply, Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
        zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, Matrix.empty_mulVec,
        WithLp.linearEquiv_symm_apply, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
        WithLp.addEquiv_symm_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring_nf!
    · ring_nf
  · rw [ContinuousLinearMap.norm_def]
    refine le_csInf ?_ ?_
    · exact ⟨‖rotM θ φ‖, norm_nonneg _, fun x => ContinuousLinearMap.le_opNorm _ _⟩
    · rintro b ⟨-, hb⟩
      specialize hb !₂[-Real.sin θ, Real.cos θ, 0]
      have h : Real.sin θ * (Real.cos θ * Real.cos φ) + -(Real.cos θ * (Real.sin θ * Real.cos φ)) = 0 := by
        ring
      simpa [rotM, rotM_mat, EuclideanSpace.norm_eq, Fin.sum_univ_succ, ←sq, h] using hb

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
  norm_num1
  simp_all only [one_div, Fin.isValue]
  apply Iff.intro
  · intro h₁ v
    simpa using h₁ (WithLp.toLp 2 fun i => if i = 0 then 0 else if i = 1 then v 0 else v 1)
  · intro h₁ v
    specialize h₁ (WithLp.toLp 2 fun i => if i = 0 then v 1 else v 2)
    simp only [Matrix.vecHead, Fin.isValue, ↓reduceIte, Matrix.vecTail, Nat.succ_eq_add_one,
      Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, one_ne_zero] at h₁
    simp only [Matrix.vecHead, Matrix.vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring_nf at h₁ ⊢
    calc _ ≤ _ := h₁
         _ ≤ _ := by
           refine mul_le_mul_of_nonneg_left ?_ hx
           exact (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity))

theorem norm_RyL_sub_RyL_eq {ε α α_ : ℝ} (hε : 0 < ε) (hα : |α - α_| ≤ ε) :
    ‖RyL α - RyL α_‖ = ‖rotR α - rotR α_‖ := by
  sorry

theorem norm_RzL_sub_RzL_eq {ε α α_ : ℝ} (hε : 0 < ε) (hα : |α - α_| ≤ ε) :
    ‖RzL α - RzL α_‖ = ‖rotR α - rotR α_‖ := by
  sorry

theorem norm_RxRy_minus_id_le {α β : ℝ} : ‖RxL α ∘L RyL β - 1‖ ≤ √(α ^ 2 + β ^ 2) := by
  sorry

theorem norm_M_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖rotM θ φ - rotM θ_ φ_‖ < √2 * ε := by
  sorry

theorem norm_X_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖vecX θ φ - vecX θ_ φ_‖ < √2 * ε := by
  sorry

theorem XPgt0 {P : ℝ³} {ε θ θ_ φ φ_ : ℝ} (hP : ‖P‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hX : √2 * ε < ⟪vecX θ_ φ_, P⟫) :
    0 < ⟪vecX θ φ, P⟫ := by
  sorry

theorem norm_M_apply_gt {ε r θ θ_ φ φ_ : ℝ} {P : ℝ³}
    (hP : ‖P‖ ≤ 1) (hε : 0 < ε) (hr : 0 < r) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hM : r + √2 * ε < ‖rotM θ_ φ_ P‖) : r < ‖rotM θ φ P‖ := by
  sorry

theorem norm_RM_sub_RM_le {ε θ θ_ φ φ_ α α_}
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) (hα : |α - α_| ≤ ε) :
    ‖rotprojRM θ φ α - rotprojRM θ_ φ_ α_‖ < √5 * ε := by
  sorry
