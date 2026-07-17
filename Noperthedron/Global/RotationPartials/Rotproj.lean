/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Noperthedron.Global.FDerivHelpers
public import Noperthedron.Global.RotationDerivs
public import Noperthedron.PoseInterval
public import Noperthedron.Global.Definitions

@[expose] public section


/-!
# Rotproj Inner Lemmas

- `rotproj_inner'`, `rotprojRM'` definitions
- **`HasFDerivAt.rotproj_inner`** (main theorem)
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma Differentiable.rotprojRM (S : ℝ³) :
    Differentiable ℝ fun (x : ℝ³)  ↦ (_root_.rotprojRM (x 1) (x 2) (x 0)) S := by
  unfold _root_.rotprojRM
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

@[fun_prop]
lemma Differentiable.rotproj_inner (S : ℝ³) (w : ℝ²) : Differentiable ℝ (rotproj_inner S w) :=
  Differentiable.inner ℝ (Differentiable.rotprojRM S) (by fun_prop)

/--
The Fréchet derivative of `fun x => rotprojRM (x 1) (x 2) (x 0) S` at `pbar.innerParams`.
Components:
- index 0 (α): rotR' α (rotM θ φ S)
- index 1 (θ): rotR α (rotMθ θ φ S)
- index 2 (φ): rotR α (rotMφ θ φ S)
-/
noncomputable
def rotprojRM' (pbar : Pose ℝ) (S : ℝ³) : ℝ³ →L[ℝ] ℝ² :=
  columnsCLM ![pbar.rotR' (pbar.rotM₁ S), pbar.rotR (pbar.rotM₁θ S), pbar.rotR (pbar.rotM₁φ S)]

/--
The Fréchet derivative of `rotproj_inner S w` at `pbar.innerParams`.
Defined as the composition of the inner product derivative with the rotprojRM derivative.
-/
noncomputable
def rotproj_inner' (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) : ℝ³ →L[ℝ] ℝ :=
  (fderivInnerCLM ℝ ((rotprojRM pbar.θ₁ pbar.φ₁ pbar.α) S, w)).comp ((rotprojRM' pbar S).prod 0)

@[simp]
lemma rotprojRM'_single_0 (pbar : Pose ℝ) (S : ℝ³) :
    (rotprojRM' pbar S) (EuclideanSpace.single 0 1) = pbar.rotR' (pbar.rotM₁ S) := by
  simp [rotprojRM']

@[simp]
lemma rotprojRM'_single_1 (pbar : Pose ℝ) (S : ℝ³) :
    (rotprojRM' pbar S) (EuclideanSpace.single 1 1) = pbar.rotR (pbar.rotM₁θ S) := by
  simp [rotprojRM']

@[simp]
lemma rotprojRM'_single_2 (pbar : Pose ℝ) (S : ℝ³) :
    (rotprojRM' pbar S) (EuclideanSpace.single 2 1) = pbar.rotR (pbar.rotM₁φ S) := by
  simp [rotprojRM']

lemma HasFDerivAt.rotproj_inner (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) :
    HasFDerivAt (rotproj_inner S w) (rotproj_inner' pbar S w) pbar.innerParams := by
  have hdiff : DifferentiableAt ℝ
      (fun x : ℝ³ => rotR (x.ofLp 0) (rotM (x.ofLp 1) (x.ofLp 2) S)) pbar.innerParams :=
    differentiableAt_rotR_rotM S pbar.innerParams
  -- The derivative is a linear map determined by its values on the standard basis,
  -- and those values were already computed in `FDerivHelpers`.
  have z1 : HasFDerivAt (fun x => (rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S)
      (rotprojRM' pbar S) pbar.innerParams := by
    have h0 : pbar.innerParams.ofLp 0 = pbar.α := by simp [Pose.innerParams]
    have h1 : pbar.innerParams.ofLp 1 = pbar.θ₁ := by simp [Pose.innerParams]
    have h2 : pbar.innerParams.ofLp 2 = pbar.φ₁ := by simp [Pose.innerParams]
    have hfd : fderiv ℝ (fun x : ℝ³ => rotR (x.ofLp 0) (rotM (x.ofLp 1) (x.ofLp 2) S))
        pbar.innerParams = rotprojRM' pbar S := by
      refine ContinuousLinearMap.coe_injective
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_)
      fin_cases i <;>
        simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          ContinuousLinearMap.coe_coe, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      · rw [fderiv_rotR_rotM_in_e0 S _ hdiff, rotprojRM'_single_0, h0, h1, h2]; rfl
      · rw [fderiv_rotR_rotM_in_e1 S _ hdiff, rotprojRM'_single_1, h0, h1, h2]; rfl
      · rw [fderiv_rotR_rotM_in_e2 S _ hdiff, rotprojRM'_single_2, h0, h1, h2]; rfl
    exact hfd ▸ hdiff.hasFDerivAt

  have step : (rotproj_inner' pbar S w) = ((fderivInnerCLM ℝ
      ((rotprojRM (pbar.innerParams.ofLp 1) (pbar.innerParams.ofLp 2) (pbar.innerParams.ofLp 0)) S, w)).comp
      ((rotprojRM' pbar S).prod 0)) := by
    simp only [rotproj_inner', Pose.innerParams, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl

  rw [step]
  exact HasFDerivAt.inner ℝ z1 (hasFDerivAt_const w pbar.innerParams)

end GlobalTheorem

end
