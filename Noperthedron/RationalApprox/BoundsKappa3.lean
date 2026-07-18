module

public import Mathlib.Algebra.Lie.OfAssociative
public import Noperthedron.PointSym
public import Noperthedron.PoseInterval
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.MatrixBounds
public import Noperthedron.Local.Prelims

public section


open scoped RealInnerProductSpace

namespace RationalApprox

variable {P Q Q_ P_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}

/-!
## Helper: vector norm difference bound

The operator norm bound `‖vecXL θ φ - vecXLℚℝ θ φ‖ ≤ κ` implies
the vector norm bound `‖vecX θ φ - vecXℚ θ φ‖ ≤ κ` because `vecX`
is the image of the unit basis vector under the column-matrix linear map `vecXL`.
-/

private lemma vecX_sub_vecXℚ_norm_le (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖vecX θ φ - vecXℚℝ θ φ‖ ≤ κ := by
  -- vecX θ φ - vecXℚ θ φ = (vecXL θ φ - vecXLℚℝ θ φ) (single 0 1)
  have h_eq : vecX θ φ - vecXℚℝ θ φ = (vecXL θ φ - vecXLℚℝ θ φ) (EuclideanSpace.single 0 1) := by
    simp [vecX, vecXℚℝ, vecXL, vecX_mat, vecXLℚℝ, vecXℚ_mat, sub_apply, Matrix.toLpLin_apply]
    ext i; fin_cases i <;> simp
  rw [h_eq]
  calc ‖(vecXL θ φ - vecXLℚℝ θ φ) (EuclideanSpace.single 0 1)‖
    _ ≤ ‖vecXL θ φ - vecXLℚℝ θ φ‖ * ‖EuclideanSpace.single (𝕜 := ℝ) 0 (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖vecXL θ φ - vecXLℚℝ θ φ‖ * 1 := by rw [PiLp.norm_single, norm_one]
    _ = ‖vecXL θ φ - vecXLℚℝ θ φ‖ := mul_one _
    _ ≤ κ := X_difference_norm_bounded θ φ hθ hφ

private lemma vecXℚ_norm_le (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖vecXℚℝ θ φ‖ ≤ 1 + κ := by
  calc ‖vecXℚℝ θ φ‖
    _ ≤ ‖vecX θ φ‖ + ‖vecX θ φ - vecXℚℝ θ φ‖ := norm_le_insert _ _
    _ = 1 + ‖vecX θ φ - vecXℚℝ θ φ‖ := by rw [Bounding.vecX_norm_one]
    _ ≤ 1 + κ := by gcongr; exact vecX_sub_vecXℚ_norm_le θ φ hθ hφ

/-!
[SY25] Lemma 49
-/

lemma bounds_kappa3_X (hP : ‖P‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) :
    ‖⟪vecX θ φ, P⟫ - ⟪vecXℚℝ θ φ, P_⟫‖ ≤ 3 * κ := by
  -- Decompose: ⟪vecX, P⟫ - ⟪vecXℚ, P_⟫ = ⟪vecX - vecXℚ, P⟫ + ⟪vecXℚ, P - P_⟫
  have decomp : ⟪vecX θ φ, P⟫ - ⟪vecXℚℝ θ φ, P_⟫ =
      ⟪vecX θ φ - vecXℚℝ θ φ, P⟫ + ⟪vecXℚℝ θ φ, P - P_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp, Real.norm_eq_abs]
  calc |⟪vecX ↑θ ↑φ - vecXℚℝ ↑θ ↑φ, P⟫ + ⟪vecXℚℝ ↑θ ↑φ, P - P_⟫|
    _ ≤ |⟪vecX ↑θ ↑φ - vecXℚℝ ↑θ ↑φ, P⟫| + |⟪vecXℚℝ ↑θ ↑φ, P - P_⟫| := abs_add_le _ _
    _ ≤ ‖vecX ↑θ ↑φ - vecXℚℝ ↑θ ↑φ‖ * ‖P‖ + ‖vecXℚℝ ↑θ ↑φ‖ * ‖P - P_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ κ * 1 + (1 + κ) * κ :=
        add_le_add
          (mul_le_mul (vecX_sub_vecXℚ_norm_le _ _ (θ.property) (φ.property))
            hP (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul (vecXℚ_norm_le _ _ (θ.property) (φ.property))
            Papprox (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 3 * κ := by unfold κ; norm_num

lemma bounds_kappa3_M (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    ‖⟪rotM θ φ P, rotM θ φ Q⟫ - ⟪rotMℚℝ θ φ P_, rotMℚℝ θ φ Q_⟫‖ ≤ 5 * κ := by
  rw [Real.norm_eq_abs]
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hMℚnorm : ‖rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (θ.property) (φ.property)
  -- Decompose: ⟪rotM P, rotM Q⟫ - ⟪rotMℚ P_, rotMℚ Q_⟫
  --   = ⟪rotM P - rotMℚ P_, rotM Q⟫ + ⟪rotMℚ P_, rotM Q - rotMℚ Q_⟫
  have decomp : ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotMℚℝ ↑θ ↑φ) Q_⟫ =
      ⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
      ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  -- Bound ‖rotM P - rotMℚ P_‖ and ‖rotM Q - rotMℚ Q_‖
  have hAP : ‖(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hMdiff hMℚnorm hP Papprox
  have hBQ : ‖(rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hMdiff hMℚnorm hQ Qapprox
  -- Bound ‖rotM Q‖
  have hMQ : ‖(rotM ↑θ ↑φ) Q‖ ≤ 1 := clm_unit_apply_le (le_of_eq (Bounding.rotM_norm_one _ _)) hQ
  -- Bound ‖rotMℚ P_‖
  have hMℚP_ : ‖(rotMℚℝ ↑θ ↑φ) P_‖ ≤ (1 + κ) * (1 + κ) :=
    approx_image_norm_le hMℚnorm hP Papprox
  calc |⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
        ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫|
    _ ≤ |⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫| +
        |⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫| := abs_add_le _ _
    _ ≤ ‖(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q‖ +
        ‖(rotMℚℝ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (2 * κ + κ ^ 2) * 1 + (1 + κ) * (1 + κ) * (2 * κ + κ ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAP (norm_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left hMQ (by norm_num [κ])))
          (mul_le_mul hMℚP_ hBQ (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 5 * κ := by unfold κ; norm_num

lemma bounds_kappa3_MQ (hQ : ‖Q‖ ≤ 1) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    |(‖rotM θ φ Q‖ - ‖rotMℚℝ θ φ Q_‖)| ≤ 3 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hMℚnorm : ‖rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (θ.property) (φ.property)
  -- Reverse triangle inequality + clm_approx_apply_sub
  calc |(‖rotM θ φ Q‖ - ‖rotMℚℝ θ φ Q_‖)|
    _ ≤ ‖rotM θ φ Q - rotMℚℝ θ φ Q_‖ := abs_norm_sub_norm_le _ _
    _ ≤ 2 * κ + κ ^ 2 := clm_approx_apply_sub hMdiff hMℚnorm hQ Qapprox
    _ ≤ 3 * κ := by unfold κ; norm_num

end RationalApprox
end
