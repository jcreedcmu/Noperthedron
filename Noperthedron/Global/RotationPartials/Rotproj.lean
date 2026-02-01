/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.FDerivHelpers
import Noperthedron.Global.Definitions

/-!
# Rotproj HasFDerivAt Lemmas

This file contains:
- `Differentiable.rotprojRM`, `Differentiable.rotproj_inner`
- `rotproj_inner'`, `rotprojRM'` definitions
- Component lemmas for rotR, rotM applications
- **`HasFDerivAt.rotproj_inner`** (main theorem)
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

/--
An explicit formula for the full derivative of rotproj_inner as a function ℝ³ → ℝ
-/
noncomputable
def rotproj_inner' (pbar : Pose) (S : ℝ³) (w : ℝ²) : ℝ³ →L[ℝ] ℝ :=
  let grad : Fin 3 → ℝ := ![
    ⟪pbar.rotR' (pbar.rotM₁ S), w⟫,
    ⟪pbar.rotR (pbar.rotM₁θ S), w⟫,
    ⟪pbar.rotR (pbar.rotM₁φ S), w⟫
  ]
  EuclideanSpace.basisFun (Fin 3) ℝ |>.toBasis.constr ℝ grad |>.toContinuousLinearMap

/--
The Fréchet derivative of `fun x => rotprojRM (x 1) (x 2) (x 0) S` at `pbar.innerParams`.
-/
noncomputable
def rotprojRM' (pbar : Pose) (S : ℝ³) : ℝ³ →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 3) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (pbar.rotR' (pbar.rotM₁ S)) i
    | 1 => (pbar.rotR (pbar.rotM₁θ S)) i
    | 2 => (pbar.rotR (pbar.rotM₁φ S)) i
  M.toEuclideanLin.toContinuousLinearMap

lemma Differentiable.rotprojRM (S : ℝ³) :
    Differentiable ℝ fun (x : ℝ³) ↦ (rotprojRM (x 1) (x 2) (x 0)) S := by
  unfold _root_.rotprojRM
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

@[fun_prop]
lemma Differentiable.rotproj_inner (S : ℝ³) (w : ℝ²) : Differentiable ℝ (rotproj_inner S w) :=
  Differentiable.inner ℝ (Differentiable.rotprojRM S) (by fun_prop)

lemma HasFDerivAt.rotproj_inner (pbar : Pose) (S : ℝ³) (w : ℝ²) :
    HasFDerivAt (rotproj_inner S w) (rotproj_inner' pbar S w) pbar.innerParams := by
  sorry

end GlobalTheorem
