import Mathlib
import Mathlib.Analysis.Complex.Trigonometric
import Noperthedron.Basic

open scoped RealInnerProductSpace Real

namespace Bounding

theorem pres_norm_imp_norm_one {f : ℝ² →L[ℝ] ℝ²} (hf : (v : ℝ²) → ‖f v‖ = ‖v‖) : ‖f‖ = 1  := by
  have decrease (x : ℝ²) : ‖f x‖ ≤ 1 * ‖x‖ := by rw [hf x]; simp
  have increase (N : ℝ) (hN : N ≥ 0) (k : ∀ (x : ℝ²), ‖f x‖ ≤ N * ‖x‖) : 1 ≤ N := by
    have z := k !₂[1,0]
    rw [hf !₂[1,0]] at z
    simp only [norm_pos_iff, ne_eq, WithLp.toLp_eq_zero, Matrix.cons_eq_zero_iff, one_ne_zero,
      Matrix.zero_empty, and_self, and_true, not_false_eq_true, le_mul_iff_one_le_left] at z;
    exact z
  refine ContinuousLinearMap.opNorm_eq_of_bounds (by norm_num) decrease increase

theorem rotR_norm_one (α : ℝ) : ‖rotR α‖ = 1 := by
  refine pres_norm_imp_norm_one ?_
  intro v
  suffices h : ‖v‖^2 = ‖rotR α v‖^2 by simp_all
  simp only [rotR, rotR_mat, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, Fin.isValue, AddChar.coe_mk,
    LinearMap.coe_toContinuousLinearMap', Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply,
    Matrix.mulVec, Matrix.of_apply, Matrix.vec2_dotProduct, neg_mul]
  convert_to _ = (v 0)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2) + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
  · ring_nf
  simp

theorem Rx_norm_one (α : ℝ) : ‖RxL α‖ = 1 := by
  sorry

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
