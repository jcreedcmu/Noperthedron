import NegativeRupert.Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Basic
import NegativeRupert.ViewPose

open scoped Matrix
open scoped Real

/--
Maybe this should be renamed something much shorter like "Pose".
I'm starting to get a feeling this is a more basic type
than the things currently called "Pose" and "ViewPose".
-/
structure LooseViewPose : Type where
  θ₁ : ℝ
  θ₂ : ℝ
  φ₁ : ℝ
  φ₂ : ℝ
  α : ℝ

instance : Coe ViewPose LooseViewPose where
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
  min : LooseViewPose
  max : LooseViewPose

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

namespace LooseViewPose

def closed_ball (p : LooseViewPose) (ε : ℝ) : PoseInterval := {
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

-- Some convenience functions for doing rotations with dot notation
-- Maybe the rotations in basic could be inlined here? It depends on whether
-- we actually use them not in the context of a LooseViewPose.

noncomputable
def rotM₁ (p : LooseViewPose) : ℝ³ →ᵃ[ℝ] ℝ² := rotM (p.θ₁) (p.φ₁)
noncomputable
def rotM₂ (p : LooseViewPose) : ℝ³ →ᵃ[ℝ] ℝ² := rotM (p.θ₂) (p.φ₂)
noncomputable
def rotR (p : LooseViewPose) : ℝ² →ᵃ[ℝ] ℝ² := _root_.rotR (p.α)

noncomputable
def rotM₁θ (p : LooseViewPose) : ℝ³ →ᵃ[ℝ] ℝ² := rotMθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θ (p : LooseViewPose) : ℝ³ →ᵃ[ℝ] ℝ² := rotMθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₁φ (p : LooseViewPose) : ℝ³ →ᵃ[ℝ] ℝ² := rotMφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂φ (p : LooseViewPose) : ℝ³ →ᵃ[ℝ] ℝ² := rotMφ (p.θ₂) (p.φ₂)
noncomputable
def rotR' (p : LooseViewPose) : ℝ² →ᵃ[ℝ] ℝ² := _root_.rotR' (p.α)

end LooseViewPose

namespace PoseInterval

def contains (iv : PoseInterval) (vp : LooseViewPose) : Prop :=
  (vp.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁) ∧
  (vp.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂) ∧
  (vp.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁) ∧
  (vp.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂) ∧
  (vp.α ∈ Set.Icc iv.min.α iv.max.α)

end PoseInterval

structure TightViewPose : Type where
  θ₁ : Set.Icc 0 (2 * π / 15)
  θ₂ : Set.Icc 0 (2 * π / 15)
  φ₁ : Set.Icc 0 π
  φ₂ : Set.Icc 0 (π/2)
  α : Set.Icc (-π/2) (π/2)

noncomputable
instance : Affines LooseViewPose where
  inner vp := rotRM vp.θ₁ vp.φ₁ vp.α
  outer vp := rotRM vp.θ₂ vp.φ₂ 0

noncomputable
instance : Affines TightViewPose where
  inner vp := rotRM vp.θ₁ vp.φ₁ vp.α
  outer vp := rotRM vp.θ₂ vp.φ₂ 0
