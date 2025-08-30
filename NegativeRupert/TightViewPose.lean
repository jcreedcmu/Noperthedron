import Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Basic

open scoped Matrix
open scoped Real

structure TightViewPose : Type where
  θ1 : Set.Icc 0 (2 * π / 15)
  θ2 : Set.Icc 0 (2 * π / 15)
  φ1 : Set.Icc 0 π
  φ2 : Set.Icc 0 (π/2)
  α : Set.Ico (-π/2) (π/2)

noncomputable
instance : Affines TightViewPose where
  inner vp := rotRM vp.θ1 vp.φ1 vp.α
  outer vp := rotRM vp.θ2 vp.φ2 0
