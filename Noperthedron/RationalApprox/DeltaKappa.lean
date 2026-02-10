import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.MatrixBounds

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P P_ : ℝ³} {Q Q_ : ℝ³} {α θ φ θ_ φ_ : Set.Icc (-4) 4} {w : ℝ²}

/-- Convert `Set.Icc` membership from `ℤ` bounds to `ℝ` bounds. -/
private lemma icc_int_to_real (x : Set.Icc ((-4 : ℤ)) 4) :
    (x : ℝ) ∈ Set.Icc ((-4 : ℝ)) 4 :=
  ⟨by exact_mod_cast x.property.1, by exact_mod_cast x.property.2⟩

/-!
[SY25] Corollary 50
-/

lemma delta_kappa (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    |‖rotR α (rotM θ φ P) - rotM θ_ φ_ Q‖ - ‖rotRℚ α (rotMℚ θ φ P) - rotMℚ θ_ φ_ Q_‖| ≤ 6 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (icc_int_to_real θ) (icc_int_to_real φ)
  have hMℚnorm : ‖rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (icc_int_to_real θ) (icc_int_to_real φ)
  have hRdiff : ‖rotR (α : ℝ) - rotRℚ (α : ℝ)‖ ≤ κ :=
    R_difference_norm_bounded _ (icc_int_to_real α)
  have hM_diff' : ‖rotM (θ_ : ℝ) (φ_ : ℝ) - rotMℚ (θ_ : ℝ) (φ_ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (icc_int_to_real θ_) (icc_int_to_real φ_)
  have hMℚnorm' : ‖rotMℚ (θ_ : ℝ) (φ_ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (icc_int_to_real θ_) (icc_int_to_real φ_)
  -- Term 1: ‖rotR(rotM P) - rotRℚ(rotMℚ P)‖ ≤ 2κ + κ²
  have term1 : ‖rotR α (rotM θ φ P) - rotRℚ α (rotMℚ θ φ P)‖ ≤ 2 * κ + κ ^ 2 := by
    calc ‖rotR α (rotM θ φ P) - rotRℚ α (rotMℚ θ φ P)‖
      _ = ‖(rotR ↑α ((rotM ↑θ ↑φ) P) - rotR ↑α ((rotMℚ ↑θ ↑φ) P)) +
            (rotR ↑α ((rotMℚ ↑θ ↑φ) P) - rotRℚ ↑α ((rotMℚ ↑θ ↑φ) P))‖ := by congr 1; abel
      _ ≤ ‖rotR ↑α ((rotM ↑θ ↑φ) P) - rotR ↑α ((rotMℚ ↑θ ↑φ) P)‖ +
            ‖rotR ↑α ((rotMℚ ↑θ ↑φ) P) - rotRℚ ↑α ((rotMℚ ↑θ ↑φ) P)‖ := norm_add_le _ _
      _ = ‖rotR ↑α ((rotM ↑θ ↑φ - rotMℚ ↑θ ↑φ) P)‖ +
            ‖(rotR ↑α - rotRℚ ↑α) ((rotMℚ ↑θ ↑φ) P)‖ := by
          simp only [map_sub, ContinuousLinearMap.sub_apply]
      _ ≤ ‖rotR (↑α)‖ * ‖(rotM ↑θ ↑φ - rotMℚ ↑θ ↑φ) P‖ +
            ‖rotR ↑α - rotRℚ ↑α‖ * ‖(rotMℚ ↑θ ↑φ) P‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ 1 * (κ * 1) + κ * ((1 + κ) * 1) := by
          apply add_le_add
          · calc ‖rotR (↑α)‖ * ‖(rotM ↑θ ↑φ - rotMℚ ↑θ ↑φ) P‖
              _ ≤ ‖rotR (↑α)‖ * (‖rotM ↑θ ↑φ - rotMℚ ↑θ ↑φ‖ * ‖P‖) :=
                  mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
              _ ≤ 1 * (κ * 1) :=
                  mul_le_mul (le_of_eq (Bounding.rotR_norm_one _))
                    (mul_le_mul hMdiff hP (norm_nonneg _) (by norm_num [κ]))
                    (by positivity) (by norm_num)
          · calc ‖rotR ↑α - rotRℚ ↑α‖ * ‖(rotMℚ ↑θ ↑φ) P‖
              _ ≤ ‖rotR ↑α - rotRℚ ↑α‖ * (‖rotMℚ ↑θ ↑φ‖ * ‖P‖) :=
                  mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
              _ ≤ κ * ((1 + κ) * 1) :=
                  mul_le_mul hRdiff
                    (mul_le_mul hMℚnorm hP (norm_nonneg _) (by norm_num [κ]))
                    (by positivity) (by norm_num [κ])
      _ = 2 * κ + κ ^ 2 := by ring
  -- Term 2: ‖rotM' Q - rotMℚ' Q_‖ ≤ 2κ + κ²
  have term2 : ‖rotM θ_ φ_ Q - rotMℚ θ_ φ_ Q_‖ ≤ 2 * κ + κ ^ 2 := by
    calc ‖rotM θ_ φ_ Q - rotMℚ θ_ φ_ Q_‖
      _ = ‖((rotM ↑θ_ ↑φ_) Q - (rotMℚ ↑θ_ ↑φ_) Q) +
            ((rotMℚ ↑θ_ ↑φ_) Q - (rotMℚ ↑θ_ ↑φ_) Q_)‖ := by congr 1; abel
      _ ≤ ‖(rotM ↑θ_ ↑φ_) Q - (rotMℚ ↑θ_ ↑φ_) Q‖ +
            ‖(rotMℚ ↑θ_ ↑φ_) Q - (rotMℚ ↑θ_ ↑φ_) Q_‖ := norm_add_le _ _
      _ = ‖(rotM ↑θ_ ↑φ_ - rotMℚ ↑θ_ ↑φ_) Q‖ + ‖(rotMℚ ↑θ_ ↑φ_) (Q - Q_)‖ := by
          rw [ContinuousLinearMap.sub_apply, map_sub]
      _ ≤ ‖rotM ↑θ_ ↑φ_ - rotMℚ ↑θ_ ↑φ_‖ * ‖Q‖ + ‖rotMℚ ↑θ_ ↑φ_‖ * ‖Q - Q_‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ κ * 1 + (1 + κ) * κ :=
          add_le_add
            (mul_le_mul hM_diff' hQ (norm_nonneg _) (by norm_num [κ]))
            (mul_le_mul hMℚnorm' Qapprox (norm_nonneg _) (by norm_num [κ]))
      _ = 2 * κ + κ ^ 2 := by ring
  -- Combine using reverse triangle inequality
  calc |‖rotR ↑α ((rotM ↑θ ↑φ) P) - (rotM ↑θ_ ↑φ_) Q‖ -
        ‖rotRℚ ↑α ((rotMℚ ↑θ ↑φ) P) - (rotMℚ ↑θ_ ↑φ_) Q_‖|
    _ ≤ ‖(rotR ↑α ((rotM ↑θ ↑φ) P) - (rotM ↑θ_ ↑φ_) Q) -
          (rotRℚ ↑α ((rotMℚ ↑θ ↑φ) P) - (rotMℚ ↑θ_ ↑φ_) Q_)‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖(rotR ↑α ((rotM ↑θ ↑φ) P) - rotRℚ ↑α ((rotMℚ ↑θ ↑φ) P)) -
          ((rotM ↑θ_ ↑φ_) Q - (rotMℚ ↑θ_ ↑φ_) Q_)‖ := by congr 1; abel
    _ ≤ ‖rotR ↑α ((rotM ↑θ ↑φ) P) - rotRℚ ↑α ((rotMℚ ↑θ ↑φ) P)‖ +
          ‖(rotM ↑θ_ ↑φ_) Q - (rotMℚ ↑θ_ ↑φ_) Q_‖ := norm_sub_le _ _
    _ ≤ (2 * κ + κ ^ 2) + (2 * κ + κ ^ 2) := add_le_add term1 term2
    _ ≤ 6 * κ := by unfold κ; norm_num
