import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P P_ : ℝ³} {α θ φ : Set.Icc (-4) 4} {w : ℝ²}

/-!
[SY25] Lemma 44
-/

lemma bounds_kappa_M (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotM θ φ P, w⟫ - ⟪rotMℚ θ φ P_, w⟫‖ ≤ 3 * κ := by
  sorry

lemma bounds_kappa_Mθ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotMθ θ φ P, w⟫ - ⟪rotMθℚ θ φ P_, w⟫‖ ≤ 3 * κ := by
  sorry

lemma bounds_kappa_Mφ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotMφ θ φ P, w⟫ - ⟪rotMφℚ θ φ P_, w⟫‖ ≤ 3 * κ := by
  sorry

lemma bounds_kappa_RM (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotM θ φ P), w⟫ - ⟪rotRℚ α (rotMℚ θ φ P_), w⟫‖ ≤ 4 * κ := by
  sorry

lemma bounds_kappa_R'M (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR' α (rotM θ φ P), w⟫ - ⟪rotR'ℚ α (rotMℚ θ φ P_), w⟫‖ ≤ 4 * κ := by
  sorry

lemma bounds_kappa_RMθ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotMθ θ φ P), w⟫ - ⟪rotRℚ α (rotMθℚ θ φ P_), w⟫‖ ≤ 4 * κ := by
  sorry

lemma bounds_kappa_RMφ (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖⟪rotR α (rotMφ θ φ P), w⟫ - ⟪rotRℚ α (rotMφℚ θ φ P_), w⟫‖ ≤ 4 * κ := by
  sorry
