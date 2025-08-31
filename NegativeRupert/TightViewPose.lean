import Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Basic
import NegativeRupert.ViewPose

open scoped Matrix
open scoped Real

structure LooseViewPose : Type where
  θ1 : ℝ
  θ2 : ℝ
  φ1 : ℝ
  φ2 : ℝ
  α : ℝ

instance : Coe ViewPose LooseViewPose where
  coe vp := {
    θ1 := vp.θ1,
    θ2 := vp.θ2,
    φ1 := vp.φ1,
    φ2 := vp.φ2,
    α := vp.α,
  }

structure PoseInterval : Type where
  min : LooseViewPose
  max : LooseViewPose

noncomputable
def tightInterval : PoseInterval where
  min := {
    θ1 := 0
    θ2 := 0
    φ1 := 0
    φ2 := 0
    α := -(π / 2)
  }
  max := {
    θ1 := 2 * π / 15
    θ2 := 2 * π / 15
    φ1 := π
    φ2 := π / 2
    α := π / 2
  }

namespace PoseInterval

def contains (iv : PoseInterval) (vp : LooseViewPose) : Prop :=
  (vp.θ1 ∈ Set.Icc iv.min.θ1 iv.max.θ1) ∧
  (vp.θ2 ∈ Set.Icc iv.min.θ2 iv.max.θ2) ∧
  (vp.φ1 ∈ Set.Icc iv.min.φ1 iv.max.φ1) ∧
  (vp.φ2 ∈ Set.Icc iv.min.φ2 iv.max.φ2) ∧
  (vp.α ∈ Set.Icc iv.min.α iv.max.α)

end PoseInterval

structure TightViewPose : Type where
  θ1 : Set.Icc 0 (2 * π / 15)
  θ2 : Set.Icc 0 (2 * π / 15)
  φ1 : Set.Icc 0 π
  φ2 : Set.Icc 0 (π/2)
  α : Set.Icc (-π/2) (π/2)

noncomputable
instance : Affines TightViewPose where
  inner vp := rotRM vp.θ1 vp.φ1 vp.α
  outer vp := rotRM vp.θ2 vp.φ2 0
