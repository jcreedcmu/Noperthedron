import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic
import Noperthedron.ViewPose
import Noperthedron.Pose

open scoped Matrix
open scoped Real

instance : Coe ViewPose Pose where
  coe vp := {
    θ₁ := vp.θ₁,
    θ₂ := vp.θ₂,
    φ₁ := vp.φ₁,
    φ₂ := vp.φ₂,
    α := vp.α,
  }

/--
Represents a closed 5d box in parameter space.
-/
structure PoseInterval : Type where
  min : Pose
  max : Pose

noncomputable
def tightInterval : PoseInterval where
  min := {
    θ₁ := 0
    θ₂ := 0
    φ₁ := 0
    φ₂ := 0
    α := -(π / 2)
  }
  max := {
    θ₁ := 2 * π / 15
    θ₂ := 2 * π / 15
    φ₁ := π
    φ₂ := π / 2
    α := π / 2
  }

namespace Pose

def closed_ball (p : Pose) (ε : ℝ) : PoseInterval := {
  min := {
    θ₁ := p.θ₁ - ε
    θ₂ := p.θ₂ - ε
    φ₁ := p.φ₁ - ε
    φ₂ := p.φ₂ - ε
    α := p.α - ε
  }
  max := {
    θ₁ := p.θ₁ + ε
    θ₂ := p.θ₂ + ε
    φ₁ := p.φ₁ + ε
    φ₂ := p.φ₂ + ε
    α := p.α + ε
  }
}

end Pose

namespace PoseInterval

def contains (iv : PoseInterval) (vp : Pose) : Prop :=
  (vp.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁) ∧
  (vp.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂) ∧
  (vp.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁) ∧
  (vp.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂) ∧
  (vp.α ∈ Set.Icc iv.min.α iv.max.α)

def center (iv : PoseInterval) : Pose where
  θ₁ := (iv.min.θ₁ + iv.max.θ₁)
  θ₂ := (iv.min.θ₂ + iv.max.θ₂)
  φ₁ := (iv.min.φ₁ + iv.max.φ₁)
  φ₂ := (iv.min.φ₂ + iv.max.φ₂)
  α := (iv.min.α + iv.max.α)

end PoseInterval

instance : Membership Pose PoseInterval where
  mem iv vp := iv.contains vp

instance : HasSubset PoseInterval where
  Subset a b := ∀ p, p ∈ a → p ∈ b

structure TightViewPose : Type where
  θ₁ : Set.Icc 0 (2 * π / 15)
  θ₂ : Set.Icc 0 (2 * π / 15)
  φ₁ : Set.Icc 0 π
  φ₂ : Set.Icc 0 (π/2)
  α : Set.Icc (-π/2) (π/2)

noncomputable
instance : PoseLike TightViewPose where
  inner vp := (rotRM vp.θ₁ vp.φ₁ vp.α).toAffineMap
  outer vp := (rotRM vp.θ₂ vp.φ₂ 0).toAffineMap
