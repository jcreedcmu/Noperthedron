import Rupert.Basic
import NegativeRupert.PoseClasses

open scoped Matrix
open scoped Real

structure ViewPose : Type where
  θ1 : Set.Ioc 0 (2 * π)
  θ2 : Set.Ioc 0 (2 * π)
  φ1 : Set.Icc 0 π
  φ2 : Set.Icc 0 π
  α : Set.Ico (-π) π

noncomputable
def e3 : Module.Basis (Fin 3) ℝ ℝ³ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

noncomputable
def R (α : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ :=
  let A : Matrix (Fin 3) (Fin 3) ℝ := sorry
  (A.toLin e3 e3).toAffineMap

noncomputable
def M (θ : ℝ) (φ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ :=
  let A : Matrix (Fin 3) (Fin 3) ℝ := sorry
  (A.toLin e3 e3).toAffineMap

noncomputable
instance : Affines ViewPose where
  inner vp := (R (vp.α)).comp (M vp.θ1 vp.φ1)
  outer vp := M vp.θ2 vp.φ2
