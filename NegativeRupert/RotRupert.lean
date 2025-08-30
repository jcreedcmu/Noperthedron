import Rupert.Basic
import NegativeRupert.Pose

open scoped Matrix

/-- The Rupert Property for a subset S of ℝ³. S has the Rupert property if there
    are rotations and translations such that one 2-dimensional "shadow" of S can
    be made to fit entirely inside the interior of another such "shadow". -/
def IsRotRupertSet (S : Set ℝ³) : Prop := ∃ p : Pose, p.IsRot ∧ p.IsRupert S
