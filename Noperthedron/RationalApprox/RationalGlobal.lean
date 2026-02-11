import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic

open scoped RealInnerProductSpace

namespace RationalApprox.GlobalTheorem

/--
A measure of how far an inner-shadow vertex S can "stick out"
-/
noncomputable
def G (p : Pose) (ε : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.innerℚ S, w⟫ - (ε * (|⟪p.rotR'ℚ (p.rotM₁ℚ S), w⟫| + |⟪p.rotRℚ (p.rotM₁θℚ S), w⟫| + |⟪p.rotRℚ (p.rotM₁φℚ S), w⟫|)
  + 9 * ε^2 / 2 + 4 * κ * (1 + 3 * ε))

/--
A measure of how far an outer-shadow vertex P can "reach" along w.
-/
noncomputable
def H (p : Pose) (ε : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ℚ P, w⟫ + ε * (|⟪p.rotM₂θℚ P, w⟫| + |⟪p.rotM₂φℚ P, w⟫|) + 2 * ε^2 + 3 * κ * (1 + 2 * ε)

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
noncomputable
def maxH (p : Pose) (poly : GoodPoly) (ε : ℝ) (w : ℝ²) : ℝ :=
  poly.vertices.image (H p ε w) |>.max' <| by
    simp only [Finset.image_nonempty]
    exact poly.nonempty

/--
A compact way of saying "the pose satisfies the rational global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyhedron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure RationalGlobalTheoremPrecondition (poly poly_ : GoodPoly)
    (happrox : κApproxPoly poly.vertices poly_.vertices) (p : Pose) (ε : ℝ) : Type where
  S : ℝ³
  S_in_poly : S ∈ poly_.vertices
  p_in_4 : fourInterval.contains p
  w : ℝ²
  w_unit : ‖w‖ = 1
  exceeds : G p ε S w > maxH p poly_ ε w

/--
[SY25] Theorem 43
-/
theorem rational_global (pbar : Pose) (ε : ℝ) (hε : ε > 0)
    (poly poly_ : GoodPoly)
    (happrox : κApproxPoly poly.vertices poly_.vertices)
    (_poly_pointsym : PointSym poly.hull)
    (pc : RationalGlobalTheoremPrecondition poly poly_ happrox pbar ε) :
    ¬ ∃ p ∈ pbar.closed_ball ε, RupertPose p poly.hull := by
  sorry
