import Noperthedron.Local
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.EpsKapSpanning

namespace RationalApprox

theorem rational_local : False := by
  sorry

/-
import Noperthedron.Local
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.EpsKapSpanning

namespace RationalApprox.LocalTheorem

theorem rational_local (P Q : Triangle)
    (cong_tri : P.Congruent Q)
    (poly : Finset ℝ³) (ne : poly.Nonempty)
    (hP : ∀ i, P i ∈ poly) (hQ : ∀ i, Q i ∈ poly)
    (radius_one : polyhedronRadius poly ne = 1)
    (p_ : Pose)
    (ε δ r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hr₁ : BoundR r ε p_ Q)
    (hδ : BoundDelta δ p_ P Q)
    (ae₁ : P.Aε p_.vecX₁ ε) (ae₂ : Q.Aε p_.vecX₂ ε)
    (span₁ : P.Spanning p_.θ₁ p_.φ₁ ε)
    (span₂ : Q.Spanning p_.θ₂ p_.φ₂ ε)
    (be : Q.Bε poly p_ ε δ r)
    : ¬∃ p ∈ p_.closed_ball ε, RupertPose p (shape_of poly |>.hull) := by
  sorry
-/
