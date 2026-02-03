/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Noperthedron.Nopert
import Noperthedron.PoseInterval

/-!
# Global Theorem Definitions

Shared definitions for the global theorem.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

noncomputable
def rotproj_inner (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫

noncomputable
def rotproj_inner_unit (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫ / ‖S‖

noncomputable
def rotproj_outer_unit (S : ℝ³) (w : ℝ²) (x : ℝ²) : ℝ :=
  ⟪rotM (x 0) (x 1) S, w⟫ / ‖S‖

noncomputable
def rotproj_outer (S : ℝ³) (w : ℝ²) (x : ℝ²) : ℝ :=
  ⟪rotM (x 0) (x 1) S, w⟫

/-- Expand rotproj_inner in terms of rotR and rotM -/
@[simp]
lemma rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : ℝ³) :
    rotproj_inner S w x = ⟪rotR (x 0) (rotM (x 1) (x 2) S), w⟫ := by
  simp [rotproj_inner, rotprojRM]

/-- rotproj_inner_unit equals rotproj_inner divided by norm -/
@[simp]
lemma rotproj_inner_unit_eq (S : ℝ³) (w : ℝ²) (x : ℝ³) :
    rotproj_inner_unit S w x = rotproj_inner S w x / ‖S‖ := by
  simp [rotproj_inner_unit, rotproj_inner]

/-- Expand rotproj_outer in terms of rotM -/
@[simp]
lemma rotproj_outer_eq (S : ℝ³) (w : ℝ²) (x : ℝ²) :
    rotproj_outer S w x = ⟪rotM (x 0) (x 1) S, w⟫ := rfl

/-- rotproj_outer_unit equals rotproj_outer divided by norm -/
@[simp]
lemma rotproj_outer_unit_eq (S : ℝ³) (w : ℝ²) (x : ℝ²) :
    rotproj_outer_unit S w x = rotproj_outer S w x / ‖S‖ := rfl

/--
An explicit formula for the full derivative of rotproj_outer as a function ℝ² → ℝ
-/
noncomputable
def rotproj_outer' (pbar : Pose) (P : ℝ³) (w : ℝ²) : ℝ² →L[ℝ] ℝ :=
  let grad : Fin 2 → ℝ := ![
    ⟪pbar.rotM₂θ P, w⟫,
    ⟪pbar.rotM₂φ P, w⟫
  ]
  EuclideanSpace.basisFun (Fin 2) ℝ |>.toBasis.constr ℝ grad |>.toContinuousLinearMap

lemma rotation_partials_exist {S : ℝ³} (S_nonzero : ‖S‖ > 0) {w : ℝ²} :
    ContDiff ℝ 2 (rotproj_inner_unit S w) := by
  refine ContDiff.div ?_ contDiff_const (fun x ↦ (ne_of_lt S_nonzero).symm)
  simp [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

lemma rotation_partials_exist_outer {S : ℝ³} (S_nonzero : ‖S‖ > 0) {w : ℝ²} :
    ContDiff ℝ 2 (rotproj_outer_unit S w) := by
  refine ContDiff.div ?_ contDiff_const (fun x ↦ (ne_of_lt S_nonzero).symm)
  simp [inner, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

end GlobalTheorem
