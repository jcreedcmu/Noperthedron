import Mathlib.Data.Real.Hom
import Noperthedron.Rupert.Basic
import Noperthedron.Rupert.Set
open Pointwise
open Matrix

/-- Projecting from ℝ³ to ℝ² is linear -/
noncomputable
def proj_xy_linear : ℝ³ →ₗ[ℝ] ℝ² :=
  {
   toFun := proj_xy,
   map_add' := by
     intro x y;
     ext i; fin_cases i <;> simp [proj_xy]
   ,
   map_smul' := by
     intro x y; ext i; fin_cases i <;> simp [proj_xy]
   }

noncomputable
def rotation_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ³ := (Matrix.toEuclideanLin rot).toAffineMap

noncomputable
def proj_xy_rotation_is_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp proj_xy_linear.toAffineMap (rotation_affine rot)

noncomputable
def full_transform_affine (off : E 2) (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp (AffineEquiv.constVAdd ℝ (E 2) off) (proj_xy_rotation_is_affine rot)
