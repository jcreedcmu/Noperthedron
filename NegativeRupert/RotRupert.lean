import Rupert.Basic

open scoped Matrix

structure Pose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

namespace Pose

def outerShadow (p : Pose) (s : Set ℝ³) : Set ℝ² :=
  { proj_xy (p.outerRot *ᵥ v) | v ∈ s }

def innerShadow (p : Pose) (s : Set ℝ³) : Set ℝ² :=
  { p.innerOffset + proj_xy (p.innerRot *ᵥ v) | v ∈ s }

/--
A candidate is "safe" if it does not admit a Rupert solution.
-/
def IsRupert (p : Pose) (s : Set ℝ³) : Prop :=
  closure (p.innerShadow s) ⊆ interior (p.outerShadow s)

/--
A pose is "safe" if it decisively does not admit a Rupert solution.
-/
def Safe (p : Pose) (s : Set ℝ³) : Prop :=
  ∃ y, y ∈ p.innerShadow s ∧ ¬ y ∈ p.outerShadow s

def IsRot (p : Pose) : Prop :=
  p.innerOffset = 0

end Pose


/-- The Rupert Property for a subset S of ℝ³. S has the Rupert property if there
    are rotations and translations such that one 2-dimensional "shadow" of S can
    be made to fit entirely inside the interior of another such "shadow". -/
def IsRotRupertSet (S : Set ℝ³) : Prop := ∃ p : Pose, p.IsRot ∧ p.IsRupert S
