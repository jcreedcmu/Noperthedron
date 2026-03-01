/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Noperthedron.RotationDerivs
import Noperthedron.Global.SecondPartialHelpers
import Noperthedron.Global.Definitions
import Noperthedron.Global.Basic

/-!
# FDeriv Helper Lemmas for Global Theorem

This file contains helper lemmas for computing fderiv in coordinate directions.
These show that fderiv f y (e_i) equals the partial derivative in direction i.

## Main Results

* `fderiv_rotR_rotM_in_e0` - fderiv of rotR ∘ rotM in direction e₀ gives rotR'
* `fderiv_rotR_rotM_in_e1` - fderiv of rotR ∘ rotM in direction e₁ gives rotR ∘ rotMθ
* `fderiv_rotR_rotM_in_e2` - fderiv of rotR ∘ rotM in direction e₂ gives rotR ∘ rotMφ
* `fderiv_rotR'_rotM_in_e0` - fderiv of rotR' ∘ rotM in direction e₀ gives -rotR
* `fderiv_rotR'_rotM_in_e1` - fderiv of rotR' ∘ rotM in direction e₁ gives rotR' ∘ rotMθ
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- Derivative of rotR' with respect to α: d/dα(rotR' α v) = -rotR α v
-- This is needed for the second derivative ∂²/∂α² of rotproj_inner
lemma HasDerivAt_rotR' (α : ℝ) (v : ℝ²) :
    HasDerivAt (rotR' · v) (-(rotR α v)) α := by
  have h_f : (rotR' · v) = (fun α' => !₂[-Real.sin α' * v 0 - Real.cos α' * v 1,
      Real.cos α' * v 0 - Real.sin α' * v 1]) := by
    ext α' i
    fin_cases i <;> simp [rotR', rotR'_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : -(rotR α v) = !₂[-Real.cos α * v 0 + Real.sin α * v 1,
      -Real.sin α * v 0 - Real.cos α * v 1] := by
    ext i
    fin_cases i <;> simp [rotR, rotR_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']
  refine hasDerivAt_lp2 ?_ ?_
  · convert hasDerivAt_sin_cos_lincomb (-v 0) (-v 1) α using 1
    · funext; ring
    · ring
  · convert hasDerivAt_cos_sin_lincomb (v 0) (-v 1) α using 1
    · funext; ring
    · ring

/-- fderiv of rotR with any M in direction e₀ gives rotR' -/
lemma fderiv_rotR_any_M_in_e0 (S : Euc(3)) (y : E 3) (M : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S))
      (rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 0 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR ((y + t • EuclideanSpace.single 0 1).ofLp 0)
        (M ((y + t • EuclideanSpace.single 0 1).ofLp 1) ((y + t • EuclideanSpace.single 0 1).ofLp 2) S) =
        rotR (y.ofLp 0 + t) (M (y.ofLp 1) (y.ofLp 2) S) by
      rw [coord_e0_same, coord_e0_at1, coord_e0_at2]]
    exact hasDerivAt_comp_add _ _ _ (HasDerivAt_rotR (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S))
  exact hline.lineDeriv

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₀ gives rotR' -/
lemma fderiv_rotR_rotM_in_e0 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) :=
  fderiv_rotR_any_M_in_e0 S y rotM hf_diff

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₂ gives rotR ∘ rotMφ -/
lemma fderiv_rotR_rotM_in_e2 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 2 1).ofLp 1) ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2 + t) S) by
      rw [coord_e2_at0, coord_e2_at1, coord_e2_same]]
    exact hasDerivAt_comp_add _ _ _ (by simpa [LinearMap.comp_toSpanSingleton] using
      ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp
        (y.ofLp 2) (hasDerivAt_rotM_φ (y.ofLp 1) (y.ofLp 2) S).hasFDerivAt).hasDerivAt)
  exact hline.lineDeriv

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₁ gives rotR ∘ rotMθ -/
lemma fderiv_rotR_rotM_in_e1 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 1 1).ofLp 1) ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotM (y.ofLp 1 + t) (y.ofLp 2) S) by
      rw [coord_e1_at0, coord_e1_same, coord_e1_at2, add_comm]]
    exact hasDerivAt_comp_add _ _ _ (by simpa [LinearMap.comp_toSpanSingleton] using
      ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp
        (y.ofLp 1) (hasDerivAt_rotM_θ (y.ofLp 1) (y.ofLp 2) S).hasFDerivAt).hasDerivAt)
  exact hline.lineDeriv

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₀ gives -rotR -/
lemma fderiv_rotR'_rotM_in_e0 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    -(rotR α (rotM θ φ S)) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (-(rotR α (rotM θ φ S))) y (EuclideanSpace.single 0 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR' ((y + t • EuclideanSpace.single 0 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 0 1).ofLp 1)
             ((y + t • EuclideanSpace.single 0 1).ofLp 2) S) =
        rotR' (y.ofLp 0 + t) (rotM θ φ S) by
      rw [coord_e0_same, coord_e0_at1, coord_e0_at2, hθ, hφ]]
    simpa [hα] using hasDerivAt_comp_add _ _ _ (HasDerivAt_rotR' α (rotM θ φ S))
  exact hline.lineDeriv

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₁ gives rotR' α (rotMθ θ φ S) -/
lemma fderiv_rotR'_rotM_in_e1 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR' α (rotMθ θ φ S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR' α (rotMθ θ φ S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR' ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 1 1).ofLp 1)
             ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR' α (rotM (θ + t) φ S) by
      rw [coord_e1_at0, coord_e1_same, coord_e1_at2, hα, hθ, hφ, add_comm]]
    exact hasDerivAt_comp_add _ _ _ (by simpa [LinearMap.comp_toSpanSingleton] using
      ((ContinuousLinearMap.hasFDerivAt (rotR' α)).comp θ (hasDerivAt_rotM_θ θ φ S).hasFDerivAt).hasDerivAt)
  exact hline.lineDeriv

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₂ gives rotR' α (rotMφ θ φ S) -/
lemma fderiv_rotR'_rotM_in_e2 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR' α (rotMφ θ φ S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR' α (rotMφ θ φ S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR' ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 2 1).ofLp 1)
             ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR' α (rotM θ (φ + t) S) by
      rw [coord_e2_at0, coord_e2_at1, coord_e2_same, hα, hθ, hφ, add_comm]]
    exact hasDerivAt_comp_add _ _ _ (by simpa [LinearMap.comp_toSpanSingleton] using
      ((ContinuousLinearMap.hasFDerivAt (rotR' α)).comp φ (hasDerivAt_rotM_φ θ φ S).hasFDerivAt).hasDerivAt)
  exact hline.lineDeriv

/-!
## fderiv of rotproj_inner in coordinate directions

These combine `fderiv_inner_const` with `fderiv_rotR_rotM_in_e*` to give
formulas for partial derivatives of rotproj_inner directly.
-/

/-- fderiv of rotproj_inner in direction e₀ -/
lemma fderiv_rotproj_inner_in_e0 (S : ℝ³) (w : ℝ²) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) =
    ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  have heq : rotproj_inner S w = fun z => ⟪rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S), w⟫ := by
    ext z; simp [rotproj_inner, rotprojRM]
  rw [heq, fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e0 S y hf_diff]

/-- fderiv of rotproj_inner in direction e₁ -/
lemma fderiv_rotproj_inner_in_e1 (S : ℝ³) (w : ℝ²) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) =
    ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  have heq : rotproj_inner S w = fun z => ⟪rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S), w⟫ := by
    ext z; simp [rotproj_inner, rotprojRM]
  rw [heq, fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e1 S y hf_diff]

/-- fderiv of rotproj_inner in direction e₂ -/
lemma fderiv_rotproj_inner_in_e2 (S : ℝ³) (w : ℝ²) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) =
    ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  have heq : rotproj_inner S w = fun z => ⟪rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S), w⟫ := by
    ext z; simp [rotproj_inner, rotprojRM]
  rw [heq, fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e2 S y hf_diff]

/-!
## nth_partial of rotproj_inner in coordinate directions

These lift the pointwise `fderiv_rotproj_inner_in_e*` to function-level equalities
of `nth_partial`, eliminating the `funext`/`congrArg` boilerplate at each use site.
-/

lemma nth_partial_rotproj_inner_e0 (S : ℝ³) (w : ℝ²) :
    nth_partial 0 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ :=
  funext fun y => fderiv_rotproj_inner_in_e0 S w y (differentiableAt_rotR_rotM S y)

lemma nth_partial_rotproj_inner_e1 (S : ℝ³) (w : ℝ²) :
    nth_partial 1 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ :=
  funext fun y => fderiv_rotproj_inner_in_e1 S w y (differentiableAt_rotR_rotM S y)

lemma nth_partial_rotproj_inner_e2 (S : ℝ³) (w : ℝ²) :
    nth_partial 2 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ :=
  funext fun y => fderiv_rotproj_inner_in_e2 S w y (differentiableAt_rotR_rotM S y)

end GlobalTheorem
