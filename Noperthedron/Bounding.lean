import Noperthedron.Basic

open scoped RealInnerProductSpace Real

namespace Bounding

theorem pres_norm_imp_norm_one {n:ℕ} [NeZero n] {f : E n →L[ℝ] E n} (hf : (v : E n) → ‖f v‖ = ‖v‖) : ‖f‖ = 1  := by
  have decrease (x : E n) : ‖f x‖ ≤ 1 * ‖x‖ := by rw [hf x]; simp
  have increase (N : ℝ) (hN : N ≥ 0) (k : ∀ (x : E n), ‖f x‖ ≤ N * ‖x‖) : 1 ≤ N := by
    let e : E n := (WithLp.toLp 2 (Pi.single 0 1))
    have he : ‖e‖ = 1 := by
      simp only [EuclideanSpace.toLp_single, EuclideanSpace.norm_single, one_mem,
        CStarRing.norm_of_mem_unitary, e]
    have z := k e; rw [hf e] at z; simp [he] at z; exact z
  refine ContinuousLinearMap.opNorm_eq_of_bounds (by norm_num) decrease increase

theorem pres_sq_norm_imp_norm_one {n:ℕ} [NeZero n] {f : E n →L[ℝ] E n} (hf : (v : E n) → ‖f v‖^2 = ‖v‖^2) : ‖f‖ = 1  := by
  refine pres_norm_imp_norm_one ?_
  intro v
  suffices h : ‖f v‖^2 = ‖v‖^2  by simp_all
  exact hf v

theorem rotR_norm_one (α : ℝ) : ‖rotR α‖ = 1 := by
  refine pres_sq_norm_imp_norm_one ?_
  intro v
  simp only [rotR, rotR_mat, PiLp.norm_sq_eq_of_L2]
  simp only [AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap', Matrix.piLp_ofLp_toEuclideanLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec2_dotProduct, Fin.isValue,
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
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec3_dotProduct, Fin.isValue,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, one_mul, zero_mul, add_zero, zero_add, neg_mul]
  ring_nf
  convert_to (v 0)^2
           + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 2)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           = _
  · ring_nf
  simp

theorem Ry_norm_one (α : ℝ) : ‖RyL α‖ = 1 := by
  sorry

theorem Rz_norm_one (α : ℝ) : ‖RzL α‖ = 1 := by
  sorry

theorem M_norm_one (θ φ : ℝ) : ‖rotM θ φ‖ = 1 := by
  sorry

theorem RaRa {ε α α_ : ℝ} (hε : 0 < ε) (hα : |α - α_| ≤ ε) :
    ‖rotR α - rotR α_‖ < ε ∧
    ‖RxL α - RxL α_‖ = ‖rotR α - rotR α_‖ ∧
    ‖RyL α - RyL α_‖ = ‖rotR α - rotR α_‖ ∧
    ‖RzL α - RzL α_‖ = ‖rotR α - rotR α_‖ := by
  sorry

theorem one_plus_cos_mul_one_plus_cos_ge {a b : ℝ} (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    2 + 2 * Real.cos √(a ^ 2 + b ^ 2) ≤ (1 + Real.cos a) * (1 + Real.cos b) := by
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
