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

namespace MatrixPose

def hull (s : Shape) : Set ℝ³ := convexHull ℝ { s.vertices i | i }

def outerShadow (p : MatrixPose) (s : Shape) : Set ℝ² :=
  { proj_xy (p.outerRot *ᵥ v) | v ∈ hull s }

def innerShadow (p : MatrixPose) (s : Shape) : Set ℝ² :=
  { p.innerOffset + proj_xy (p.innerRot *ᵥ v) | v ∈ hull s }

/--
A candidate is "safe" if it does not admit a Rupert solution.
-/
def IsRupert (p : MatrixPose) (s : Shape) : Prop :=
  closure (p.innerShadow s) ⊆ interior (p.outerShadow s)

/--
A pose is "safe" if it decisively does not admit a Rupert solution.
-/
def Safe (p : MatrixPose) (s : Shape) : Prop :=
  ∃ y, y ∈ p.innerShadow s ∧ ¬ y ∈ p.outerShadow s

end MatrixPose

/--
A matrix-format pose together with a shape. This is enough data to
make being "safe" a meaningful property, see MatrixCand.Safe below.
-/
structure MatrixCand : Type where
  pose : MatrixPose
  shape : Shape

namespace MatrixCand

def hull (c : MatrixCand) : Set ℝ³ := MatrixPose.hull c.shape
def innerOffset (c : MatrixCand) : ℝ² :=  c.pose.innerOffset
def outerShadow (c : MatrixCand) : Set ℝ² := c.pose.outerShadow c.shape
def innerShadow (c : MatrixCand) : Set ℝ² := c.pose.innerShadow c.shape

/--
A candidate is "safe" if it does not admit a Rupert solution.
-/
def Safe (c : MatrixCand) : Prop := c.pose.Safe c.shape

end MatrixCand
