import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.Cast
import Noperthedron.RationalApprox.MatrixBounds

open scoped RealInnerProductSpace

namespace RationalApprox

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
  rw [← inner_sub_left, show R (A P) - Rℚ (Aℚ P_) = R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_) by simp]
  have hAP_diff : ‖A P - Aℚ P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hAdiff hAℚnorm hP approx
  have hAℚP_ : ‖Aℚ P_‖ ≤ (1 + κ) * (1 + κ) := approx_image_norm_le hAℚnorm hP approx
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

section rational

variable {P : ℝ³} {P_ : Fin 3 → ℚ} {α θ φ : Set.Icc (-4 : ℚ) 4} {w : Fin 2 → ℚ}

/-! ## Rational `bounds_kappa` lemmas ([SY25] Lemma 44)

Each lemma bounds the difference between a real inner product (using the exact
real rotations) and the cast of a rational dot product (using the rational
matrix-mulVec versions).
-/

lemma bounds_kappa_RM
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotM θ φ P), toR2 w⟫ - rotRℚ α (rotMℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotRℚ, rotMℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (M_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_R'M
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR' α (rotM θ φ P), toR2 w⟫ - rotR'ℚ α (rotMℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotR'ℚℝ (α:ℝ) (rotMℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotR'ℚ α (rotMℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotR'ℚ, rotMℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotR'ℚ_mat_castℝ α) (rotMℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR'_norm_one _))
    (R'_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (M_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_RMθ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotMθ θ φ P), toR2 w⟫ - rotRℚ α (rotMθℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMθℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMθℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotRℚ, rotMθℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMθℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mθℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_RMφ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotMφ θ φ P), toR2 w⟫ - rotRℚ α (rotMφℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMφℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotRℚ, rotMφℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_R'Mθ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR' α (rotMθ θ φ P), toR2 w⟫ - rotR'ℚ α (rotMθℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotR'ℚℝ (α:ℝ) (rotMθℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotR'ℚ α (rotMθℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotR'ℚ, rotMθℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotR'ℚ_mat_castℝ α) (rotMθℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR'_norm_one _))
    (R'_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mθℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_R'Mφ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR' α (rotMφ θ φ P), toR2 w⟫ - rotR'ℚ α (rotMφℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotR'ℚℝ (α:ℝ) (rotMφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotR'ℚ α (rotMφℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotR'ℚ, rotMφℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotR'ℚ_mat_castℝ α) (rotMφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR'_norm_one _))
    (R'_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_RMθθ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotMθθ θ φ P), toR2 w⟫ - rotRℚ α (rotMθθℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMθθℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMθθℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotRℚ, rotMθθℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMθθℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mθθℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθθ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_RMθφ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotMθφ θ φ P), toR2 w⟫ - rotRℚ α (rotMθφℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMθφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMθφℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotRℚ, rotMθφℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMθφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mθφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_RMφφ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotMφφ θ φ P), toR2 w⟫ - rotRℚ α (rotMφφℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMφφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMφφℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotRℚ, rotMφφℚ, Matrix.toLin'_apply]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMφφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mφφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mφφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_M
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotM θ φ P, toR2 w⟫ - rotMℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotMℚ, Matrix.toLin'_apply]
    exact inner_one_bridge _ _ (rotMℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (M_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mθ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotMθ θ φ P, toR2 w⟫ - rotMθℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMθℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMθℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotMθℚ, Matrix.toLin'_apply]
    exact inner_one_bridge _ _ (rotMθℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mθℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mφ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotMφ θ φ P, toR2 w⟫ - rotMφℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMφℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotMφℚ, Matrix.toLin'_apply]
    exact inner_one_bridge _ _ (rotMφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mθθ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotMθθ θ φ P, toR2 w⟫ - rotMθθℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMθθℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMθθℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotMθθℚ, Matrix.toLin'_apply]
    exact inner_one_bridge _ _ (rotMθθℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mθθℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθθ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mθφ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotMθφ θ φ P, toR2 w⟫ - rotMθφℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMθφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMθφℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotMθφℚ, Matrix.toLin'_apply]
    exact inner_one_bridge _ _ (rotMθφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mθφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mφφ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotMφφ θ φ P, toR2 w⟫ - rotMφφℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMφφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMφφℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    simp only [rotMφφℚ, Matrix.toLin'_apply]
    exact inner_one_bridge _ _ (rotMφφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mφφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mφφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

end rational
