/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Noperthedron.Global.SymbolicRotationSemantics
import Noperthedron.Global.RotationDerivs
import Noperthedron.PoseInterval
import Noperthedron.Global.Definitions

/-!
# Rotproj Inner Lemmas

- `rotproj_inner'`, `rotprojRM'` definitions
- **`HasFDerivAt.rotproj_inner`** (main theorem)
- `nth_partial_rotproj_inner_e0/e1/e2`, instances of the symbolic bridge
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma ContDiff.rotprojRM {k : WithTop ℕ∞} (S : ℝ³) :
    ContDiff ℝ k fun (x : ℝ³) ↦ (_root_.rotprojRM (x 1) (x 2) (x 0)) S := by
  unfold _root_.rotprojRM
  exact contDiff_rotR_comp (by fun_prop)
    (contDiff_rotM_comp (by fun_prop) (by fun_prop) contDiff_const)

@[fun_prop]
lemma ContDiff.rotproj_inner {k : WithTop ℕ∞} (S : ℝ³) (w : ℝ²) :
    ContDiff ℝ k (rotproj_inner S w) :=
  ContDiff.inner ℝ (ContDiff.rotprojRM S) contDiff_const

lemma Differentiable.rotprojRM (S : ℝ³) :
    Differentiable ℝ fun (x : ℝ³)  ↦ (_root_.rotprojRM (x 1) (x 2) (x 0)) S :=
  (ContDiff.rotprojRM (k := 1) S).differentiable one_ne_zero

@[fun_prop]
lemma Differentiable.rotproj_inner (S : ℝ³) (w : ℝ²) : Differentiable ℝ (rotproj_inner S w) :=
  (ContDiff.rotproj_inner (k := 1) S w).differentiable one_ne_zero

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
  -- The derivative is the column map of the three partial derivatives.
  have z1 : HasFDerivAt (fun x => (rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S)
      (rotprojRM' pbar S) pbar.innerParams := by
    have zplain := hasFDerivAt_three_params
      (fun α θ φ => rotR α (rotM θ φ S)) pbar.innerParams
      (rotR' pbar.α (rotM pbar.θ₁ pbar.φ₁ S))
      (rotR pbar.α (rotMθ pbar.θ₁ pbar.φ₁ S))
      (rotR pbar.α (rotMφ pbar.θ₁ pbar.φ₁ S))
      (by
        simpa [_root_.rotprojRM] using
          (Differentiable.rotprojRM S).differentiableAt)
      (by simpa [Pose.innerParams] using HasDerivAt_rotR pbar.α (rotM pbar.θ₁ pbar.φ₁ S))
      (by
        simpa [Pose.innerParams, Function.comp_def] using
          (ContinuousLinearMap.hasFDerivAt (rotR pbar.α)).comp_hasDerivAt pbar.θ₁
            (hasDerivAt_rotM_θ pbar.θ₁ pbar.φ₁ S))
      (by
        simpa [Pose.innerParams, Function.comp_def] using
          (ContinuousLinearMap.hasFDerivAt (rotR pbar.α)).comp_hasDerivAt pbar.φ₁
            (hasDerivAt_rotM_φ pbar.θ₁ pbar.φ₁ S))
    simpa [rotprojRM, rotprojRM', Pose.innerParams, Pose.rotR, Pose.rotR',
      Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ] using zplain

  have step : (rotproj_inner' pbar S w) = ((fderivInnerCLM ℝ
      ((rotprojRM (pbar.innerParams.ofLp 1) (pbar.innerParams.ofLp 2) (pbar.innerParams.ofLp 0)) S, w)).comp
      ((rotprojRM' pbar S).prod 0)) := by
    simp only [rotproj_inner', Pose.innerParams, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl

  rw [step]
  exact HasFDerivAt.inner ℝ z1 (hasFDerivAt_const w pbar.innerParams)

/-!
## First partials of `rotproj_inner`, via the symbolic bridge

`rotproj_inner S w` is the evaluation of the base symbolic term, so its coordinate
partials are instances of `SymbolicRotation.iterPartial_eval_eq`; the symbolic side of
each instance is discharged by `decide`.
-/

/-- `rotproj_inner` is the evaluation of the base symbolic term. -/
lemma rotproj_inner_eq_baseTerm (S : ℝ³) (w : ℝ²) :
    rotproj_inner S w =
      fun y : E 3 =>
        ⟪(SymbolicRotation.baseTerm.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫ :=
  rfl

lemma nth_partial_rotproj_inner_e0 (S : ℝ³) (w : ℝ²) :
    nth_partial 0 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  rw [rotproj_inner_eq_baseTerm]
  exact SymbolicRotation.iterPartial_eval_eq [0]
    (t' := ⟨.pos, .r', .m⟩) (by decide) S w

lemma nth_partial_rotproj_inner_e1 (S : ℝ³) (w : ℝ²) :
    nth_partial 1 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  rw [rotproj_inner_eq_baseTerm]
  exact SymbolicRotation.iterPartial_eval_eq [1]
    (t' := ⟨.pos, .r, .mθ⟩) (by decide) S w

lemma nth_partial_rotproj_inner_e2 (S : ℝ³) (w : ℝ²) :
    nth_partial 2 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  rw [rotproj_inner_eq_baseTerm]
  exact SymbolicRotation.iterPartial_eval_eq [2]
    (t' := ⟨.pos, .r, .mφ⟩) (by decide) S w

end GlobalTheorem
