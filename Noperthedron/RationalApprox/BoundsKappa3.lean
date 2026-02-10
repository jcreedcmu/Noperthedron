import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.MatrixBounds
import Noperthedron.Local.Prelims

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P Q Q_ P_ : ℝ³} {α θ φ : Set.Icc (-4) 4} {w : ℝ²}

/-!
## Helper: vector norm difference bound

The operator norm bound `‖vecXL θ φ - vecXLℚ θ φ‖ ≤ κ` implies
the vector norm bound `‖vecX θ φ - vecXℚ θ φ‖ ≤ κ` because `vecX`
is the image of the unit basis vector under the column-matrix linear map `vecXL`.
-/

private lemma vecX_sub_vecXℚ_norm_le (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖vecX θ φ - vecXℚ θ φ‖ ≤ κ := by
  -- vecX θ φ - vecXℚ θ φ = (vecXL θ φ - vecXLℚ θ φ) (single 0 1)
  have h_eq : vecX θ φ - vecXℚ θ φ = (vecXL θ φ - vecXLℚ θ φ) (EuclideanSpace.single 0 1) := by
    simp [vecX, vecXℚ, vecXL, vecX_mat, vecXLℚ, vecXℚ_mat, ContinuousLinearMap.sub_apply,
      Matrix.toEuclideanLin_apply]
    ext i; fin_cases i <;> simp
  rw [h_eq]
  calc ‖(vecXL θ φ - vecXLℚ θ φ) (EuclideanSpace.single 0 1)‖
    _ ≤ ‖vecXL θ φ - vecXLℚ θ φ‖ * ‖EuclideanSpace.single (𝕜 := ℝ) 0 (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖vecXL θ φ - vecXLℚ θ φ‖ * 1 := by rw [EuclideanSpace.norm_single, norm_one]
    _ = ‖vecXL θ φ - vecXLℚ θ φ‖ := mul_one _
    _ ≤ κ := X_difference_norm_bounded θ φ hθ hφ

private lemma vecXℚ_norm_le (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖vecXℚ θ φ‖ ≤ 1 + κ := by
  calc ‖vecXℚ θ φ‖
    _ ≤ ‖vecX θ φ‖ + ‖vecX θ φ - vecXℚ θ φ‖ := norm_le_insert _ _
    _ = 1 + ‖vecX θ φ - vecXℚ θ φ‖ := by rw [vecX_norm_one]
    _ ≤ 1 + κ := by gcongr; exact vecX_sub_vecXℚ_norm_le θ φ hθ hφ

/-!
[SY25] Lemma 49
-/

lemma bounds_kappa3_X (hP : ‖P‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) :
    ‖⟪vecX θ φ, P⟫ - ⟪vecXℚ θ φ, P_⟫‖ ≤ 3 * κ := by
  -- Decompose: ⟪vecX, P⟫ - ⟪vecXℚ, P_⟫ = ⟪vecX - vecXℚ, P⟫ + ⟪vecXℚ, P - P_⟫
  have decomp : ⟪vecX θ φ, P⟫ - ⟪vecXℚ θ φ, P_⟫ =
      ⟪vecX θ φ - vecXℚ θ φ, P⟫ + ⟪vecXℚ θ φ, P - P_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp, Real.norm_eq_abs]
  calc |⟪vecX ↑θ ↑φ - vecXℚ ↑θ ↑φ, P⟫ + ⟪vecXℚ ↑θ ↑φ, P - P_⟫|
    _ ≤ |⟪vecX ↑θ ↑φ - vecXℚ ↑θ ↑φ, P⟫| + |⟪vecXℚ ↑θ ↑φ, P - P_⟫| := abs_add_le _ _
    _ ≤ ‖vecX ↑θ ↑φ - vecXℚ ↑θ ↑φ‖ * ‖P‖ + ‖vecXℚ ↑θ ↑φ‖ * ‖P - P_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ κ * 1 + (1 + κ) * κ :=
        add_le_add
          (mul_le_mul (vecX_sub_vecXℚ_norm_le _ _ (icc_int_to_real θ) (icc_int_to_real φ))
            hP (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul (vecXℚ_norm_le _ _ (icc_int_to_real θ) (icc_int_to_real φ))
            Papprox (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 3 * κ := by unfold κ; norm_num

lemma bounds_kappa3_M (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    ‖⟪rotM θ φ P, rotM θ φ Q⟫ - ⟪rotMℚ θ φ P_, rotMℚ θ φ Q_⟫‖ ≤ 5 * κ := by
  rw [Real.norm_eq_abs]
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ)
  have hMℚnorm : ‖rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ)
  -- Decompose: ⟪rotM P, rotM Q⟫ - ⟪rotMℚ P_, rotMℚ Q_⟫
  --   = ⟪rotM P - rotMℚ P_, rotM Q⟫ + ⟪rotMℚ P_, rotM Q - rotMℚ Q_⟫
  have decomp : ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚ ↑θ ↑φ) P_, (rotMℚ ↑θ ↑φ) Q_⟫ =
      ⟪(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
      ⟪(rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  -- Bound ‖rotM P - rotMℚ P_‖ and ‖rotM Q - rotMℚ Q_‖
  have hAP : ‖(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hMdiff hMℚnorm hP Papprox
  have hBQ : ‖(rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hMdiff hMℚnorm hQ Qapprox
  -- Bound ‖rotM Q‖
  have hMQ : ‖(rotM ↑θ ↑φ) Q‖ ≤ 1 := by
    have h := ContinuousLinearMap.le_opNorm (rotM ↑θ ↑φ) Q
    rw [Bounding.rotM_norm_one, one_mul] at h; linarith
  -- Bound ‖rotMℚ P_‖
  have hP_ : ‖P_‖ ≤ 1 + κ := by linarith [norm_le_insert P P_]
  have hMℚP_ : ‖(rotMℚ ↑θ ↑φ) P_‖ ≤ (1 + κ) * (1 + κ) := by
    calc ‖(rotMℚ ↑θ ↑φ) P_‖
      _ ≤ ‖rotMℚ ↑θ ↑φ‖ * ‖P_‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 + κ) * (1 + κ) :=
          mul_le_mul hMℚnorm hP_ (norm_nonneg _) (by norm_num [κ])
  calc |⟪(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
        ⟪(rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_⟫|
    _ ≤ |⟪(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫| +
        |⟪(rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_⟫| := abs_add_le _ _
    _ ≤ ‖(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q‖ +
        ‖(rotMℚ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (2 * κ + κ ^ 2) * 1 + (1 + κ) * (1 + κ) * (2 * κ + κ ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAP (norm_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left hMQ (by norm_num [κ])))
          (mul_le_mul hMℚP_ hBQ (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 5 * κ := by unfold κ; norm_num

lemma bounds_kappa3_MQ (hQ : ‖Q‖ ≤ 1) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    |(‖rotM θ φ Q‖ - ‖rotMℚ θ φ Q_‖)| ≤ 3 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ)
  have hMℚnorm : ‖rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ)
  -- Reverse triangle inequality + clm_approx_apply_sub
  calc |(‖rotM θ φ Q‖ - ‖rotMℚ θ φ Q_‖)|
    _ ≤ ‖rotM θ φ Q - rotMℚ θ φ Q_‖ := abs_norm_sub_norm_le _ _
    _ ≤ 2 * κ + κ ^ 2 := clm_approx_apply_sub hMdiff hMℚnorm hQ Qapprox
    _ ≤ 3 * κ := by unfold κ; norm_num
