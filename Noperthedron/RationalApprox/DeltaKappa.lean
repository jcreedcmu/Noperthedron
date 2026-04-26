import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.MatrixBounds

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P : ℝ³} {Q Q_ : ℝ³} {α θ φ θ_ φ_ : Set.Icc (-4 : ℝ) 4}

/-!
[SY25] Corollary 50
-/

lemma delta_kappa (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    |‖rotR α (rotM θ φ P) - rotM θ_ φ_ Q‖ - ‖rotRℚℝ α (rotMℚℝ θ φ P) - rotMℚℝ θ_ φ_ Q_‖| ≤ 6 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hRdiff : ‖rotR (α : ℝ) - rotRℚℝ (α : ℝ)‖ ≤ κ :=
    R_difference_norm_bounded _ (α.property)
  -- Term 1: ‖rotR(rotM P) - rotRℚ(rotMℚ P)‖ ≤ 2κ + κ²
  -- Decompose at the R level: A = rotR, Aℚ = rotRℚ, P = rotM P, P_ = rotMℚ P
  have term1 : ‖rotR α (rotM θ φ P) - rotRℚℝ α (rotMℚℝ θ φ P)‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hRdiff (Rℚ_norm_bounded _ (α.property))
      (clm_unit_apply_le (le_of_eq (Bounding.rotM_norm_one _ _)) hP)
      (by rw [show (rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P = (rotM ↑θ ↑φ - rotMℚℝ ↑θ ↑φ) P from
              (ContinuousLinearMap.sub_apply _ _ _).symm]
          calc ‖(rotM ↑θ ↑φ - rotMℚℝ ↑θ ↑φ) P‖
            _ ≤ ‖rotM ↑θ ↑φ - rotMℚℝ ↑θ ↑φ‖ * ‖P‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ κ * 1 := mul_le_mul hMdiff hP (norm_nonneg _) (by norm_num [κ])
            _ = κ := mul_one κ)
  -- Term 2: ‖rotM' Q - rotMℚ' Q_‖ ≤ 2κ + κ²
  have term2 : ‖rotM θ_ φ_ Q - rotMℚℝ θ_ φ_ Q_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub (M_difference_norm_bounded _ _ (θ_.property) (φ_.property))
      (Mℚ_norm_bounded (θ_.property) (φ_.property)) hQ Qapprox
  -- Combine using reverse triangle inequality
  calc |‖rotR ↑α ((rotM ↑θ ↑φ) P) - (rotM ↑θ_ ↑φ_) Q‖ -
        ‖rotRℚℝ ↑α ((rotMℚℝ ↑θ ↑φ) P) - (rotMℚℝ ↑θ_ ↑φ_) Q_‖|
    _ ≤ ‖(rotR ↑α ((rotM ↑θ ↑φ) P) - (rotM ↑θ_ ↑φ_) Q) -
          (rotRℚℝ ↑α ((rotMℚℝ ↑θ ↑φ) P) - (rotMℚℝ ↑θ_ ↑φ_) Q_)‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖(rotR ↑α ((rotM ↑θ ↑φ) P) - rotRℚℝ ↑α ((rotMℚℝ ↑θ ↑φ) P)) -
          ((rotM ↑θ_ ↑φ_) Q - (rotMℚℝ ↑θ_ ↑φ_) Q_)‖ := by congr 1; abel
    _ ≤ ‖rotR ↑α ((rotM ↑θ ↑φ) P) - rotRℚℝ ↑α ((rotMℚℝ ↑θ ↑φ) P)‖ +
          ‖(rotM ↑θ_ ↑φ_) Q - (rotMℚℝ ↑θ_ ↑φ_) Q_‖ := norm_sub_le _ _
    _ ≤ (2 * κ + κ ^ 2) + (2 * κ + κ ^ 2) := add_le_add term1 term2
    _ ≤ 6 * κ := by unfold κ; norm_num
