import Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Basic
import NegativeRupert.ViewPose

open scoped Matrix
open scoped Real

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
instance : Affines TightViewPose where
  inner vp := rotRM vp.θ₁ vp.φ₁ vp.α
  outer vp := rotRM vp.θ₂ vp.φ₂ 0
