import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic

open scoped RealInnerProductSpace

namespace RationalApprox

variable {P P_ : ℝ³} {Q Q_ : ℝ³} {α θ φ θ_ φ_ : Set.Icc (-4) 4} {w : ℝ²}

/-!
[SY25] Corollary 50
-/

lemma delta_kappa (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    |‖rotR α (rotM θ φ P) - rotM θ_ φ_ Q‖ - ‖rotRℚ α (rotMℚ θ φ P) - rotMℚ θ_ φ_ Q_‖| ≤ 6 * κ := by
  sorry
