import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.MatrixBounds

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P P_ : ℝ³} {α θ φ : Set.Icc (-4) 4} {w : ℝ²}

/-!
## Helper lemma

The 3κ bound pattern: for any pair of continuous linear maps `A, Aℚ` where
`‖A - Aℚ‖ ≤ κ`, `‖Aℚ‖ ≤ 1 + κ`, and points `P, P_` with
`‖P‖ ≤ 1`, `‖P - P_‖ ≤ κ`, we get `|⟪A P, w⟫ - ⟪Aℚ P_, w⟫| ≤ 3κ`.
-/

private lemma inner_three_kappa {E F : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [NormedSpace ℝ E]
    {A Aℚ : E →L[ℝ] F} {P P_ : E} {w : F}
    (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hAdiff : ‖A - Aℚ‖ ≤ κ) (hP : ‖P‖ ≤ 1)
    (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖@inner ℝ F _ (A P) w - @inner ℝ F _ (Aℚ P_) w‖ ≤ 3 * κ := by
  rw [← inner_sub_left]
  calc ‖@inner ℝ F _ (A P - Aℚ P_) w‖
    _ ≤ ‖A P - Aℚ P_‖ * ‖w‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = ‖A P - Aℚ P_‖ := by rw [hw, mul_one]
    _ ≤ 3 * κ := (clm_approx_apply_sub hAdiff hAℚnorm hP approx).trans (by unfold κ; norm_num)

/-!
[SY25] Lemma 44
-/

lemma bounds_kappa_M (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotM θ φ P, w⟫ - ⟪rotMℚ θ φ P_, w⟫‖ ≤ 3 * κ :=
  inner_three_kappa
    (Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_Mθ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotMθ θ φ P, w⟫ - ⟪rotMθℚ θ φ P_, w⟫‖ ≤ 3 * κ :=
  inner_three_kappa
    (Mθℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (Mθ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_Mφ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotMφ θ φ P, w⟫ - ⟪rotMφℚ θ φ P_, w⟫‖ ≤ 3 * κ :=
  inner_three_kappa
    (Mφℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (Mφ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

/-!
## 4κ bounds

For the composed maps R ∘ A, we decompose:
  R(A P) - Rℚ(Aℚ P_) = R(A P - Aℚ P_) + (R - Rℚ)(Aℚ P_)

This gives ≤ ‖R‖ * ‖A P - Aℚ P_‖ + ‖R - Rℚ‖ * ‖Aℚ P_‖
-/

private lemma inner_four_kappa {E F G : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A Aℚ : E →L[ℝ] F} {R Rℚ : F →L[ℝ] G} {P P_ : E} {w : G}
    (hRnorm : ‖R‖ ≤ 1)
    (hRdiff : ‖R - Rℚ‖ ≤ κ)
    (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hAdiff : ‖A - Aℚ‖ ≤ κ)
    (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖@inner ℝ G _ (R (A P)) w - @inner ℝ G _ (Rℚ (Aℚ P_)) w‖ ≤ 4 * κ := by
  rw [← inner_sub_left, show R (A P) - Rℚ (Aℚ P_) = R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_) from by
    simp [map_sub, ContinuousLinearMap.sub_apply]]
  have hAP_diff : ‖A P - Aℚ P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hAdiff hAℚnorm hP approx
  have hAℚP_ : ‖Aℚ P_‖ ≤ (1 + κ) * (1 + κ) := by
    have hP_ : ‖P_‖ ≤ 1 + κ := by linarith [norm_le_insert P P_]
    calc ‖Aℚ P_‖
      _ ≤ ‖Aℚ‖ * ‖P_‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 + κ) * (1 + κ) :=
          mul_le_mul hAℚnorm hP_ (norm_nonneg _) (by norm_num [κ])
  calc ‖@inner ℝ G _ (R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)) w‖
    _ ≤ ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖ * ‖w‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖ := by rw [hw, mul_one]
    _ ≤ ‖R (A P - Aℚ P_)‖ + ‖(R - Rℚ) (Aℚ P_)‖ := norm_add_le _ _
    _ ≤ ‖R‖ * ‖A P - Aℚ P_‖ + ‖R - Rℚ‖ * ‖Aℚ P_‖ := by
        gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (2 * κ + κ ^ 2) + κ * ((1 + κ) * (1 + κ)) := by
        have : (0 : ℝ) ≤ κ := by unfold κ; norm_num
        gcongr
    _ ≤ 4 * κ := by unfold κ; norm_num

lemma bounds_kappa_RM (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotM θ φ P), w⟫ - ⟪rotRℚ α (rotMℚ θ φ P_), w⟫‖ ≤ 4 * κ :=
  inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (icc_int_to_real α))
    (Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_R'M (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR' α (rotM θ φ P), w⟫ - ⟪rotR'ℚ α (rotMℚ θ φ P_), w⟫‖ ≤ 4 * κ :=
  inner_four_kappa
    (le_of_eq (Bounding.rotR'_norm_one _))
    (R'_difference_norm_bounded _ (icc_int_to_real α))
    (Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_RMθ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotMθ θ φ P), w⟫ - ⟪rotRℚ α (rotMθℚ θ φ P_), w⟫‖ ≤ 4 * κ :=
  inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (icc_int_to_real α))
    (Mθℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (Mθ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_RMφ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotMφ θ φ P), w⟫ - ⟪rotRℚ α (rotMφℚ θ φ P_), w⟫‖ ≤ 4 * κ :=
  inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (icc_int_to_real α))
    (Mφℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (Mφ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw
