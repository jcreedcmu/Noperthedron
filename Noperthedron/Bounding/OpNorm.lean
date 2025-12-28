import Noperthedron.Basic

namespace Bounding

theorem norm_one_of_preserves_norm {n m : ℕ} [NeZero n] {f : E n →L[ℝ] E m} (hf : (v : E n) → ‖f v‖ = ‖v‖) :
    ‖f‖ = 1 := by
  have decrease (x : E n) : ‖f x‖ ≤ 1 * ‖x‖ := by rw [hf x]; simp
  have increase (N : ℝ) (hN : N ≥ 0) (k : ∀ (x : E n), ‖f x‖ ≤ N * ‖x‖) : 1 ≤ N := by
    let e : E n := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have z := k e; rw [hf, he, mul_one] at z; exact z
  exact ContinuousLinearMap.opNorm_eq_of_bounds (by norm_num) decrease increase

theorem norm_one_of_preserves_sq_norm {n m : ℕ} [NeZero n] {f : E n →L[ℝ] E m}
    (hf : (v : E n) → ‖f v‖^2 = ‖v‖^2) : ‖f‖ = 1 := by
  refine norm_one_of_preserves_norm ?_
  intro v
  suffices h : ‖f v‖^2 = ‖v‖^2 by simp_all
  exact hf v

theorem rotR_norm_one (α : ℝ) : ‖rotR α‖ = 1 := by
  refine norm_one_of_preserves_sq_norm ?_
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

theorem Rx_preserves_norm (α : ℝ) :
    ∀ (v : E 3), ‖(RxL α) v‖ = ‖v‖ := by
  intro v
  suffices h : ‖(RxL α) v‖^2 = ‖v‖^2  by simp_all
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

theorem Rx_norm_one (α : ℝ) : ‖RxL α‖ = 1 :=
  norm_one_of_preserves_norm (Rx_preserves_norm α)

theorem Rx_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RxL α).comp A‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply, Rx_preserves_norm]

theorem Ry_preserves_norm (α : ℝ) :
    ∀ (v : E 3), ‖(RyL α) v‖ = ‖v‖ := by
  intro v
  suffices h : ‖(RyL α) v‖^2 = ‖v‖^2  by simp_all
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

theorem Ry_norm_one (α : ℝ) : ‖RyL α‖ = 1 :=
  norm_one_of_preserves_norm (Ry_preserves_norm α)

theorem Ry_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RyL α).comp A‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply, Ry_preserves_norm]

theorem Rz_preserves_norm (α : ℝ) :
    ∀ (v : E 3), ‖(RzL α) v‖ = ‖v‖ := by
  intro v
  suffices h : ‖(RzL α) v‖^2 = ‖v‖^2  by simp_all
  simp only [RzL, Rz_mat, PiLp.norm_sq_eq_of_L2]
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
  norm_one_of_preserves_norm (Rz_preserves_norm α)

theorem Rz_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RzL α).comp A‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply, Rz_preserves_norm]

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

theorem lemma9 {d : Fin 3} (α : ℝ) : ‖rot3 d α‖ = 1 := by
  fin_cases d
  all_goals simp only [rot3]
  · exact Rx_norm_one α
  · exact Ry_norm_one α
  · exact Rz_norm_one α

theorem reduceL_norm : ‖reduceL‖ = 1 := by
  have h₁ : reduceL = rotM 0 0 := by simp [rotM, reduceL, rotM_mat]
  rw [h₁]
  exact Bounding.rotM_norm_one 0 0

end Bounding
