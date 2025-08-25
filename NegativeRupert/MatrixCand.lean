import NegativeRupert.Basic

open scoped Matrix

/--
One pose consisting of two rotations and an offset
which is a candidate for evidence that a shape is rupert.
-/
structure MatrixPose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

/--
A matrix-format pose together with a shape. This is enough data to
make being "safe" a meaningful property, see MatrixCand.Safe below.
-/
structure MatrixCand : Type where
  config : MatrixPose
  shape : Shape

namespace MatrixCand

def hull (c : MatrixCand) : Set ℝ³ := convexHull ℝ { c.shape.vertices i | i }

def innerOffset (c : MatrixCand) : ℝ² :=
  c.config.innerOffset

def outerShadow (c : MatrixCand) : Set ℝ² :=
  { proj_xy (c.config.outerRot *ᵥ p) | p ∈ c.hull }

def innerShadow (c : MatrixCand) : Set ℝ² :=
  { c.innerOffset + proj_xy (c.config.innerRot *ᵥ p) | p ∈ c.hull }

/--
A candidate is "safe" if it does not admit a Rupert solution.
-/
def Safe (w : MatrixCand) : Prop :=
 ∃ y, y ∈ w.innerShadow ∧ ¬ y ∈ w.outerShadow

end MatrixCand
