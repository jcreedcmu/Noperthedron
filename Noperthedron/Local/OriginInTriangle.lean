import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Local.Prelims

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/--
Determinant of two 2D vectors.
-/
noncomputable def det2 (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0

/--
Relate determinant to inner product with rotated vector.
-/
lemma det2_eq_inner_rot (u v : EuclideanSpace ℝ (Fin 2)) : det2 u v = ⟪rotR (π/2) u, v⟫ := by
  -- By definition of determinant, we know that
  simp only [det2, Fin.isValue, rotR, rotR_mat, AddChar.coe_mk, Real.cos_pi_div_two,
    Real.sin_pi_div_two, LinearMap.coe_toContinuousLinearMap']
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Fin.isValue, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.cons_mulVec,
    Matrix.cons_dotProduct, zero_mul, neg_mul, one_mul, Matrix.dotProduct_of_isEmpty, add_zero,
    zero_add, Matrix.empty_mulVec, star_trivial, Matrix.dotProduct_cons, mul_neg]
  ring!

/--
Identity relating three 2D vectors via determinants.
-/
lemma det2_identity (A B C : EuclideanSpace ℝ (Fin 2)) :
    (det2 B C) • A + (det2 C A) • B + (det2 A B) • C = 0 := by
  ext i
  fin_cases i
  · simp only [det2, Fin.isValue, Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.zero_apply]
    linarith
  · simp only [det2, Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.zero_apply]
    ring

/-- [SY25] Lemma 26 -/
theorem origin_in_triangle {A B C : Euc(2)}
    (hA : 0 < ⟪rotR (π/2) A, B⟫) (hB : 0 < ⟪rotR (π/2) B, C⟫) (hC : 0 < ⟪rotR (π/2) C, A⟫) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a • A + b • B + c • C = 0 := by
  have h_linear_relation : (det2 B C) • A + (det2 C A) • B + (det2 A B) • C = 0 :=
    det2_identity A B C
  rw [← det2_eq_inner_rot] at hA hB hC
  exact ⟨det2 B C, det2 C A, det2 A B, hB, hC, hA, h_linear_relation⟩
