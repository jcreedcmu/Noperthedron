import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 21 -/
theorem pythagoras {θ φ : ℝ} (P : Euc(3)) :
    ‖rotM θ φ P‖ ^ 2 = ‖P‖ ^ 2 - ⟪vecX θ φ, P⟫ ^ 2 := by
  simp only [rotM, rotM_mat, neg_mul, LinearMap.coe_toContinuousLinearMap',
    EuclideanSpace.norm_sq_eq, Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.mulVec,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_dotProduct, Matrix.vecHead,
    Matrix.vecTail, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, Finset.univ_unique,
    Fin.default_eq_zero, Matrix.cons_val_succ, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, inner, vecX, RCLike.inner_apply, Real.ringHom_apply]
  grind [Real.sin_sq]

/-- [SY25] Lemma 24 -/
theorem abs_sub_inner_bars_le {m n : ℕ} (A B A_ B_ : Euc(m) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(m)) :
    |⟪A P₁, B P₂⟫ - ⟪A_ P₁, B_ P₂⟫| ≤
    ‖P₁‖ * ‖P₂‖ * (‖A - A_‖ * ‖B_‖ + ‖A_‖ * ‖B - B_‖ + ‖A - A_‖ * ‖B - B_‖) := by
  have h₁ := calc
    ⟪A P₁, B P₂⟫ = ⟪(A - A_) P₁ + A_ P₁, (B - B_) P₂ + B_ P₂⟫ := by simp
               _ = ⟪(A - A_) P₁, B_ P₂⟫ + ⟪A_ P₁, (B - B_) P₂⟫ +
                   ⟪(A - A_) P₁, (B - B_) P₂⟫ + ⟪A_ P₁, B_ P₂⟫ :=
                 by simp only [inner_add_left, inner_add_right]
                    ring
  -- Then the inequality follows from the triangle inequality,
  -- the Cauchy-Schwarz inequality and the submultiplicativity of ‖.‖:
  calc
    _ ≤ |⟪(A - A_) P₁, B_ P₂⟫| + |⟪A_ P₁, (B - B_) P₂⟫| + |⟪(A - A_) P₁, (B - B_) P₂⟫| :=
      by grind
    _ ≤ ‖(A - A_) P₁‖ * ‖B_ P₂‖ + ‖A_ P₁‖ * ‖(B - B_) P₂‖ + ‖(A - A_) P₁‖ * ‖(B - B_) P₂‖ :=
      by simp only [←Real.norm_eq_abs]
         grw [norm_inner_le_norm, norm_inner_le_norm, norm_inner_le_norm]
    _ ≤ _ :=
      by grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm,
              ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm]
         linarith only

/-- [SY25] Lemma 25 -/
theorem abs_sub_inner_le {m n : ℕ} (A B : Euc(m) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(m)) :
    |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤ ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (‖A‖ + ‖B‖ + ‖A - B‖) := by
  -- Exactly the same proof as the one for `abs_sub_inner_bars_le` yields:
  have h₁ : |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤
      ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (2 * ‖B‖ + ‖A - B‖) := by
    grind [abs_sub_inner_bars_le]
  -- Exchanging A and B, however, also gives the same inequality with 2 * ‖A‖ instead
  -- of 2 * ‖B‖.
  have h₂ : |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤
      ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (2 * ‖A‖ + ‖A - B‖) := by
    simp only [norm_sub_rev A B, abs_sub_comm ⟪A P₁, A P₂⟫ ⟪B P₁, B P₂⟫]
    grind [abs_sub_inner_bars_le]
  -- Taking the arithmetic mean of these two upper bounds produces the desired
  -- symmetric inequality.
  grind
