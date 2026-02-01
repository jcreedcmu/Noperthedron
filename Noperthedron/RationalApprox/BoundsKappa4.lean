import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic

open scoped RealInnerProductSpace

namespace RationalApprox

variable (P Q P_ Q_ : ℝ³) (α θ φ : Set.Icc (-4) 4) (ε : ℝ)

/-!
[SY25] Corollary 51
-/

noncomputable
def bounds_kappa4_A := (⟪rotM θ φ P, rotM θ φ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
  ((‖rotM θ φ P‖ + √2 * ε) * (‖rotM θ φ (P - Q)‖ + 2 * √2 * ε))

noncomputable
def bounds_kappa4_Aℚ (s : UpperSqrt) :=
  (⟪rotMℚ θ φ P_, rotMℚ θ φ (P_ - Q_)⟫ - 10 * κ - 2 * ε * (‖P_ - Q_‖ + 2 * κ) * (√2 + ε)) /
  ((s.norm (rotMℚ θ φ P_) + √2 * ε + 3 * κ) * (s.norm (rotMℚ θ φ (P_ - Q_)) + 2 * √2 * ε + 6 * κ))

lemma bounds_kappa4 (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ)
    (ε : ℝ) (hε : 0 < ε) (s : UpperSqrt) :
    bounds_kappa4_Aℚ P_ Q_ θ φ ε s ≤ bounds_kappa4_A P Q θ φ ε := by
  sorry
