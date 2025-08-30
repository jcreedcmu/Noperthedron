import Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Basic

open scoped Matrix
open scoped Real

structure ViewPose : Type where
  θ1 : Set.Ioc 0 (2 * π)
  θ2 : Set.Ioc 0 (2 * π)
  φ1 : Set.Icc 0 π
  φ2 : Set.Icc 0 π
  α : Set.Ico (-π) π

noncomputable
instance : Affines ViewPose where
  inner vp := (rotR (vp.α)).comp (rotM vp.θ1 vp.φ1)
  outer vp := rotM vp.θ2 vp.φ2
