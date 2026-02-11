import Noperthedron.Local
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.EpsKapSpanning

namespace RationalApprox.LocalTheorem
open Local (Triangle)
open scoped RealInnerProductSpace Real

/--
If we have a triangle `P` in `poly`, yield the corresponding
triangle in `poly_` which κ-approximates P.
-/
def transportTri {poly poly_ : GoodPoly} {P : Triangle}
    (hP : ∀ i, P i ∈ poly.vertices)
    (hpoly : κApproxPoly poly.vertices poly_.vertices) : Triangle :=
  fun i => hpoly.bijection ⟨P i, hP i⟩

/--
Condition A_ε^ℚ from [SY25] Theorem 48
-/
def _root_.Local.Triangle.Aεℚ (X : ℝ³) (P_ : Triangle) (ε : ℝ) : Prop :=
  ∃ σ ∈ ({-1, 1} : Set ℤ), ∀ i : Fin 3, (-1)^σ * ⟪X, P_ i⟫ > √2 * ε + 3 * κ

noncomputable
def _root_.Local.Triangle.Bεℚ.lhs (v₁ v₂ : Euc(3)) (p : Pose) (ε : ℝ) (su : UpperSqrt) : ℝ :=
   (⟪p.rotM₂ℚ v₁, p.rotM₂ℚ (v₁ - v₂)⟫ - 10 * κ - 2 * ε * (su.norm (v₁ - v₂) + 2 * κ) * (√2 + ε))
   / ((su.norm (p.rotM₂ℚ v₁) + √2 * ε + 3 * κ) * (su.norm (p.rotM₂ℚ (v₁ - v₂)) + 2 * √2 * ε + 6 * κ))

/--
Condition B_ε^ℚ from [SY25] Theorem 48
-/
def _root_.Local.Triangle.Bεℚ (Q : Triangle) (poly : Finset Euc(3)) (p : Pose) (ε δ r : ℝ) (su : UpperSqrt) : Prop :=
  ∀ i : Fin 3, ∀ v ∈ poly, v ≠ Q i →
    (δ + √5 * ε) / r < Triangle.Bεℚ.lhs (Q i) v p ε su

/-- The condition on δ -/
def BoundDeltaℚ (δ : ℝ) (p : Pose) (P Q : Triangle) (su : UpperSqrt) : Prop :=
  ∀ i : Fin 3, δ ≥ su.norm (p.rotR (p.rotM₁ℚ (P i)) - p.rotM₂ℚ (Q i))/2 + 3 * κ

/-- The condition on r -/
def BoundRℚ (r ε : ℝ) (p : Pose) (Q : Triangle) (sl : LowerSqrt) : Prop :=
  ∀ i : Fin 3, sl.norm (p.rotM₂ℚ (Q i)) > r + √2 * ε + 3 * κ

/--
[SY25] Theorem 48 "The Rational Local Theorem"
-/
theorem rational_local (poly poly_ : GoodPoly)
    (hpoly : κApproxPoly poly.vertices poly_.vertices)
    (P Q : Triangle)
    (cong_tri : P.Congruent Q)
    (hP : ∀ i, P i ∈ poly.vertices) (hQ : ∀ i, Q i ∈ poly.vertices)
    (p_ : Pose) (hp : fourInterval.contains p_)
    (ε δ r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (su : UpperSqrt) (sl : LowerSqrt)
    (hr₁ : BoundRℚ r ε p_ (transportTri hQ hpoly) sl)
    (hδ : BoundDeltaℚ δ p_ (transportTri hP hpoly) (transportTri hQ hpoly) su)
    (ae₁ : (transportTri hP hpoly).Aεℚ p_.vecX₁ℚ ε) (ae₂ : (transportTri hQ hpoly).Aεℚ p_.vecX₂ℚ ε)
    (span₁ : (transportTri hP hpoly).κSpanning p_.θ₁ p_.φ₁ ε)
    (span₂ : (transportTri hQ hpoly).κSpanning p_.θ₂ p_.φ₂ ε)
    (be : (transportTri hQ hpoly).Bεℚ poly_.vertices p_ ε δ r su)
    : ¬∃ p ∈ p_.closed_ball ε, RupertPose p poly.hull := by
  sorry
