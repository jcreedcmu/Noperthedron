import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.MatrixBounds

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P P_ : ℝ³} {α θ φ : Set.Icc (-4) 4} {w : ℝ²}

/-- Convert `Set.Icc` membership from `ℤ` bounds to `ℝ` bounds. -/
private lemma icc_int_to_real (x : Set.Icc ((-4 : ℤ)) 4) :
    (x : ℝ) ∈ Set.Icc ((-4 : ℝ)) 4 := by
  exact ⟨by exact_mod_cast x.property.1, by exact_mod_cast x.property.2⟩

/-!
## Helper lemma

The 3κ bound pattern: for any pair of continuous linear maps `A, Aℚ` where
`‖A - Aℚ‖ ≤ κ`, `‖A‖ ≤ 1`, `‖Aℚ‖ ≤ 1 + κ`, and points `P, P_` with
`‖P‖ ≤ 1`, `‖P - P_‖ ≤ κ`, we get `‖A P - Aℚ P_‖ ≤ 2κ + κ² ≤ 3κ`.
-/

private lemma inner_three_kappa {E F : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [NormedSpace ℝ E]
    {A Aℚ : E →L[ℝ] F} {P P_ : E} {w : F}
    (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hAdiff : ‖A - Aℚ‖ ≤ κ) (hP : ‖P‖ ≤ 1)
    (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖@inner ℝ F _ (A P) w - @inner ℝ F _ (Aℚ P_) w‖ ≤ 3 * κ := by
  -- Step 1: ⟪A P, w⟫ - ⟪Aℚ P_, w⟫ = ⟪A P - Aℚ P_, w⟫
  rw [← inner_sub_left]
  -- Step 2: |⟪v, w⟫| ≤ ‖v‖ * ‖w‖, then simplify with ‖w‖ = 1
  have key : ‖A P - Aℚ P_‖ ≤ 3 * κ := by
    -- A P - Aℚ P_ = (A P - Aℚ P) + (Aℚ P - Aℚ P_)
    have split : A P - Aℚ P_ = (A P - Aℚ P) + (Aℚ P - Aℚ P_) := by
      abel
    rw [split]
    calc ‖(A P - Aℚ P) + (Aℚ P - Aℚ P_)‖
      _ ≤ ‖A P - Aℚ P‖ + ‖Aℚ P - Aℚ P_‖ := norm_add_le _ _
      _ = ‖(A - Aℚ) P‖ + ‖Aℚ (P - P_)‖ := by
          rw [ContinuousLinearMap.sub_apply, map_sub]
      _ ≤ ‖A - Aℚ‖ * ‖P‖ + ‖Aℚ‖ * ‖P - P_‖ := by
          gcongr
          · exact ContinuousLinearMap.le_opNorm _ _
          · exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ κ * 1 + (1 + κ) * κ := by
          have hκ : (0 : ℝ) ≤ κ := by unfold κ; norm_num
          gcongr
      _ ≤ 3 * κ := by unfold κ; norm_num
  calc ‖@inner ℝ F _ (A P - Aℚ P_) w‖
    _ ≤ ‖A P - Aℚ P_‖ * ‖w‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = ‖A P - Aℚ P_‖ * 1 := by rw [hw]
    _ = ‖A P - Aℚ P_‖ := mul_one _
    _ ≤ 3 * κ := key

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
    ‖⟪rotMθ θ φ P, w⟫ - ⟪rotMθℚ θ φ P_, w⟫‖ ≤ 3 * κ := by
  -- Need Mθℚ_norm_bounded inline
  have hMθℚ : ‖rotMθℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ := by
    calc ‖rotMθℚ (θ : ℝ) (φ : ℝ)‖
      _ ≤ ‖rotMθ (θ : ℝ) (φ : ℝ)‖ + ‖rotMθ (θ : ℝ) (φ : ℝ) - rotMθℚ (θ : ℝ) (φ : ℝ)‖ :=
          norm_le_insert _ _
      _ ≤ 1 + ‖rotMθ (θ : ℝ) (φ : ℝ) - rotMθℚ (θ : ℝ) (φ : ℝ)‖ := by
          gcongr; exact Bounding.rotMθ_norm_le_one _ _
      _ ≤ 1 + κ := by
          gcongr; exact Mθ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ)
  exact inner_three_kappa
    hMθℚ
    (Mθ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_Mφ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotMφ θ φ P, w⟫ - ⟪rotMφℚ θ φ P_, w⟫‖ ≤ 3 * κ := by
  -- Need Mφℚ_norm_bounded inline
  have hMφℚ : ‖rotMφℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ := by
    calc ‖rotMφℚ (θ : ℝ) (φ : ℝ)‖
      _ ≤ ‖rotMφ (θ : ℝ) (φ : ℝ)‖ + ‖rotMφ (θ : ℝ) (φ : ℝ) - rotMφℚ (θ : ℝ) (φ : ℝ)‖ :=
          norm_le_insert _ _
      _ ≤ 1 + ‖rotMφ (θ : ℝ) (φ : ℝ) - rotMφℚ (θ : ℝ) (φ : ℝ)‖ := by
          gcongr; exact Bounding.rotMφ_norm_le_one _ _
      _ ≤ 1 + κ := by
          gcongr; exact Mφ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ)
  exact inner_three_kappa
    hMφℚ
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
    (hRnorm : ‖R‖ ≤ 1) (_hRℚnorm : ‖Rℚ‖ ≤ 1 + κ)
    (hRdiff : ‖R - Rℚ‖ ≤ κ)
    (_hAnorm : ‖A‖ ≤ 1) (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hAdiff : ‖A - Aℚ‖ ≤ κ)
    (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖@inner ℝ G _ (R (A P)) w - @inner ℝ G _ (Rℚ (Aℚ P_)) w‖ ≤ 4 * κ := by
  rw [← inner_sub_left]
  -- R(A P) - Rℚ(Aℚ P_) = R(A P - Aℚ P_) + (R - Rℚ)(Aℚ P_)
  have decomp : R (A P) - Rℚ (Aℚ P_) = R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_) := by
    simp [map_sub, ContinuousLinearMap.sub_apply]
  rw [decomp]
  -- Bound ‖A P - Aℚ P_‖
  have hAP_diff : ‖A P - Aℚ P_‖ ≤ 2 * κ + κ ^ 2 := by
    have split : A P - Aℚ P_ = (A P - Aℚ P) + (Aℚ P - Aℚ P_) := by abel
    rw [split]
    calc ‖(A P - Aℚ P) + (Aℚ P - Aℚ P_)‖
      _ ≤ ‖A P - Aℚ P‖ + ‖Aℚ P - Aℚ P_‖ := norm_add_le _ _
      _ = ‖(A - Aℚ) P‖ + ‖Aℚ (P - P_)‖ := by
          rw [ContinuousLinearMap.sub_apply, map_sub]
      _ ≤ ‖A - Aℚ‖ * ‖P‖ + ‖Aℚ‖ * ‖P - P_‖ := by
          gcongr
          · exact ContinuousLinearMap.le_opNorm _ _
          · exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ κ * 1 + (1 + κ) * κ := by
          have hκ : (0 : ℝ) ≤ κ := by unfold κ; norm_num
          gcongr
      _ = 2 * κ + κ ^ 2 := by ring
  -- Bound ‖Aℚ P_‖
  have hAℚP_ : ‖Aℚ P_‖ ≤ (1 + κ) * (1 + κ) := by
    have hκ : (0 : ℝ) ≤ κ := by unfold κ; norm_num
    have hP_ : ‖P_‖ ≤ 1 + κ := by
      calc ‖P_‖ ≤ ‖P‖ + ‖P - P_‖ := norm_le_insert P P_
        _ ≤ 1 + κ := by linarith
    calc ‖Aℚ P_‖
      _ ≤ ‖Aℚ‖ * ‖P_‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 + κ) * (1 + κ) := by
          apply mul_le_mul hAℚnorm hP_ (norm_nonneg _) (by linarith)
  have key : ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖ ≤ 4 * κ := by
    have hκ : (0 : ℝ) ≤ κ := by unfold κ; norm_num
    calc ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖
      _ ≤ ‖R (A P - Aℚ P_)‖ + ‖(R - Rℚ) (Aℚ P_)‖ := norm_add_le _ _
      _ ≤ ‖R‖ * ‖A P - Aℚ P_‖ + ‖R - Rℚ‖ * ‖Aℚ P_‖ := by
          gcongr
          · exact ContinuousLinearMap.le_opNorm _ _
          · exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (2 * κ + κ ^ 2) + κ * ((1 + κ) * (1 + κ)) := by
          have hκ2 : (0 : ℝ) ≤ κ := by unfold κ; norm_num
          gcongr
      _ ≤ 4 * κ := by unfold κ; norm_num
  calc ‖@inner ℝ G _ (R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)) w‖
    _ ≤ ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖ * ‖w‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖ := by rw [hw, mul_one]
    _ ≤ 4 * κ := key

lemma bounds_kappa_RM (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotM θ φ P), w⟫ - ⟪rotRℚ α (rotMℚ θ φ P_), w⟫‖ ≤ 4 * κ :=
  inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (Rℚ_norm_bounded _ (icc_int_to_real α))
    (R_difference_norm_bounded _ (icc_int_to_real α))
    (le_of_eq (Bounding.rotM_norm_one _ _))
    (Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_R'M (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR' α (rotM θ φ P), w⟫ - ⟪rotR'ℚ α (rotMℚ θ φ P_), w⟫‖ ≤ 4 * κ := by
  have hR'ℚ : ‖rotR'ℚ (α : ℝ)‖ ≤ 1 + κ := by
    calc ‖rotR'ℚ (α : ℝ)‖
      _ ≤ ‖rotR' (α : ℝ)‖ + ‖rotR' (α : ℝ) - rotR'ℚ (α : ℝ)‖ := norm_le_insert _ _
      _ = 1 + ‖rotR' (α : ℝ) - rotR'ℚ (α : ℝ)‖ := by rw [Bounding.rotR'_norm_one]
      _ ≤ 1 + κ := by gcongr; exact R'_difference_norm_bounded _ (icc_int_to_real α)
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR'_norm_one _))
    hR'ℚ
    (R'_difference_norm_bounded _ (icc_int_to_real α))
    (le_of_eq (Bounding.rotM_norm_one _ _))
    (Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ))
    (M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_RMθ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotMθ θ φ P), w⟫ - ⟪rotRℚ α (rotMθℚ θ φ P_), w⟫‖ ≤ 4 * κ := by
  have hMθℚ : ‖rotMθℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ := by
    calc ‖rotMθℚ (θ : ℝ) (φ : ℝ)‖
      _ ≤ ‖rotMθ (θ : ℝ) (φ : ℝ)‖ + ‖rotMθ (θ : ℝ) (φ : ℝ) - rotMθℚ (θ : ℝ) (φ : ℝ)‖ :=
          norm_le_insert _ _
      _ ≤ 1 + ‖rotMθ (θ : ℝ) (φ : ℝ) - rotMθℚ (θ : ℝ) (φ : ℝ)‖ := by
          gcongr; exact Bounding.rotMθ_norm_le_one _ _
      _ ≤ 1 + κ := by
          gcongr; exact Mθ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ)
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (Rℚ_norm_bounded _ (icc_int_to_real α))
    (R_difference_norm_bounded _ (icc_int_to_real α))
    (Bounding.rotMθ_norm_le_one _ _)
    hMθℚ
    (Mθ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw

lemma bounds_kappa_RMφ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotMφ θ φ P), w⟫ - ⟪rotRℚ α (rotMφℚ θ φ P_), w⟫‖ ≤ 4 * κ := by
  have hMφℚ : ‖rotMφℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ := by
    calc ‖rotMφℚ (θ : ℝ) (φ : ℝ)‖
      _ ≤ ‖rotMφ (θ : ℝ) (φ : ℝ)‖ + ‖rotMφ (θ : ℝ) (φ : ℝ) - rotMφℚ (θ : ℝ) (φ : ℝ)‖ :=
          norm_le_insert _ _
      _ ≤ 1 + ‖rotMφ (θ : ℝ) (φ : ℝ) - rotMφℚ (θ : ℝ) (φ : ℝ)‖ := by
          gcongr; exact Bounding.rotMφ_norm_le_one _ _
      _ ≤ 1 + κ := by
          gcongr; exact Mφ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ)
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (Rℚ_norm_bounded _ (icc_int_to_real α))
    (R_difference_norm_bounded _ (icc_int_to_real α))
    (Bounding.rotMφ_norm_le_one _ _)
    hMφℚ
    (Mφ_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ))
    hP approx hw
