import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic

open scoped Matrix
open scoped Real

/- TODO: Better name "Bounded Pose" or something? -/
structure ViewPose : Type where
  θ₁ : Set.Ico 0 (2 * π)
  θ₂ : Set.Ico 0 (2 * π)
  φ₁ : Set.Icc 0 π
  φ₂ : Set.Icc 0 π
  α : Set.Ico (-π) π

noncomputable
instance : Affines ViewPose where
  inner vp := (rotRM vp.θ₁ vp.φ₁ vp.α).toAffineMap
  outer vp := (rotRM vp.θ₂ vp.φ₂ 0).toAffineMap
