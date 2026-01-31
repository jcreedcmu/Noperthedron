import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P Q Q_ P_ : ℝ³} {α θ φ : Set.Icc (-4) 4} {w : ℝ²}

/-!
[SY25] Lemma 49
-/

lemma bounds_kappa3_X (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    ‖⟪vecX θ φ, P⟫ - ⟪vecXℚ θ φ, P_⟫‖ ≤ 3 * κ := by
  sorry

lemma bounds_kappa3_M (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    ‖⟪rotM θ φ P, rotM θ φ Q⟫ - ⟪rotMℚ θ φ P_, rotMℚ θ φ Q_⟫‖ ≤ 5 * κ := by
  sorry

lemma bounds_kappa3_MQ (hQ : ‖Q‖ ≤ 1) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    |(‖rotM θ φ Q‖ - ‖rotMℚ θ φ Q_‖)| ≤ 3 * κ := by
  sorry
