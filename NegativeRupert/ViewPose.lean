import Rupert.Basic

open scoped Matrix
open scoped Real

structure ViewPose : Type where
  θ1 : Set.Ioc 0 (2 * π)
  θ2 : Set.Ioc 0 (2 * π)
  φ1 : Set.Icc 0 π
  φ2 : Set.Icc 0 π
  α : Set.Ico (-π) π

namespace ViewPose


end ViewPose
