/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationPartials.RotMOuter
import Noperthedron.Global.Basic
import Noperthedron.Global.SecondPartialHelpers

/-!
# Second Partial Outer Lemmas

This file contains:
- `outer_second_partial_A` definition
- **`second_partial_inner_rotM_outer`** (4 cases: θθ, θφ, φθ, φφ)
- **`rotation_partials_bounded_outer`**

Helper lemmas `comp_norm_le_one`, `neg_comp_norm_le_one`, `inner_bound_helper` are imported
from SecondPartialHelpers.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## The A[i,j] table for outer second partials

For the outer function (2 variables: θ, φ), we have:
| i\j |    0 (θ)        |    1 (φ)        |
|-----|-----------------|-----------------|
|  0  | rotMθθ θ φ      | rotMθφ θ φ      |
|  1  | rotMθφ θ φ      | rotMφφ θ φ      |

All have operator norm ≤ 1.
-/

/-- The operator A[i,j] for second partials of the outer rotation projection. -/
noncomputable def outer_second_partial_A (θ φ : ℝ) (i j : Fin 2) : ℝ³ →L[ℝ] ℝ² :=
  match i, j with
  | 0, 0 => rotMθθ θ φ
  | 0, 1 => rotMθφ θ φ
  | 1, 0 => rotMθφ θ φ
  | 1, 1 => rotMφφ θ φ

/-- All A[i,j] have operator norm ≤ 1 for outer partials. -/
lemma outer_second_partial_A_norm_le (θ φ : ℝ) (i j : Fin 2) :
    ‖outer_second_partial_A θ φ i j‖ ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact Bounding.rotMθθ_norm_le_one θ φ
  · exact Bounding.rotMθφ_norm_le_one θ φ
  · exact Bounding.rotMθφ_norm_le_one θ φ
  · exact Bounding.rotMφφ_norm_le_one θ φ

/-!
## Helper lemmas: first partials of ⟪rotM S, w⟫ in coordinate directions
-/

private lemma fderiv_rotM_inner_e0 (S : ℝ³) (w : ℝ²) (y : E 2) :
    (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
      (EuclideanSpace.single 0 1) = ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w y _ (Differentiable.rotM_outer S y)]
  set pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩
  have hpbar : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
  have : fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) y = rotM' pbar S :=
    (HasFDerivAt.rotM_outer pbar S).fderiv ▸ congrArg _ hpbar.symm
  rw [this]; congr 1; ext i
  simp only [rotM'_apply, EuclideanSpace.single_apply, ↓reduceIte,
    show (1 : Fin 2) ≠ 0 from by decide]
  ring

private lemma fderiv_rotM_inner_e1 (S : ℝ³) (w : ℝ²) (y : E 2) :
    (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
      (EuclideanSpace.single 1 1) = ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w y _ (Differentiable.rotM_outer S y)]
  set pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩
  have hpbar : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
  have : fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) y = rotM' pbar S :=
    (HasFDerivAt.rotM_outer pbar S).fderiv ▸ congrArg _ hpbar.symm
  rw [this]; congr 1; ext i
  simp only [rotM'_apply, EuclideanSpace.single_apply, ↓reduceIte,
    show (0 : Fin 2) ≠ 1 from by decide]
  ring

/-!
## Private lemma: second partials as inner products
-/

private lemma second_partial_rotM_outer_eq (S : ℝ³) (w : ℝ²) (x : E 2) (i j : Fin 2) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x = ⟪A S, w⟫ := by
  fin_cases i <;> fin_cases j
  · -- (0, 0): rotMθθ
    refine ⟨rotMθθ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθθ_norm_le_one _ _, ?_⟩
    let θ := x.ofLp 0; let φ := x.ofLp 1
    unfold nth_partial
    show (fderiv ℝ (fun y => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) x) (EuclideanSpace.single 0 1) = ⟪rotMθθ θ φ S, w⟫
    rw [congrArg (fderiv ℝ · x) (funext (fderiv_rotM_inner_e0 S w))]
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθ_outer S x)]
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    rw [show fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x = rotMθ' pbar S from
      (hpbar ▸ HasFDerivAt.rotMθ_outer pbar S).fderiv]
    congr 1; ext i
    simp only [rotMθ'_apply, EuclideanSpace.single_apply, ↓reduceIte,
      show (1 : Fin 2) ≠ 0 from by decide, hpbar_def]
    ring
  · -- (0, 1): rotMθφ
    refine ⟨rotMθφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθφ_norm_le_one _ _, ?_⟩
    let θ := x.ofLp 0; let φ := x.ofLp 1
    unfold nth_partial
    show (fderiv ℝ (fun y => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) x) (EuclideanSpace.single 0 1) = ⟪rotMθφ θ φ S, w⟫
    rw [congrArg (fderiv ℝ · x) (funext (fderiv_rotM_inner_e1 S w))]
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφ_outer S x)]
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    rw [show fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x = rotMφ' pbar S from
      (hpbar ▸ HasFDerivAt.rotMφ_outer pbar S).fderiv]
    congr 1; ext i
    simp only [rotMφ'_apply, EuclideanSpace.single_apply, ↓reduceIte,
      show (1 : Fin 2) ≠ 0 from by decide, hpbar_def]
    ring
  · -- (1, 0): rotMθφ
    refine ⟨rotMθφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθφ_norm_le_one _ _, ?_⟩
    let θ := x.ofLp 0; let φ := x.ofLp 1
    unfold nth_partial
    show (fderiv ℝ (fun y => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) x) (EuclideanSpace.single 1 1) = ⟪rotMθφ θ φ S, w⟫
    rw [congrArg (fderiv ℝ · x) (funext (fderiv_rotM_inner_e0 S w))]
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθ_outer S x)]
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    rw [show fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x = rotMθ' pbar S from
      (hpbar ▸ HasFDerivAt.rotMθ_outer pbar S).fderiv]
    congr 1; ext i
    simp only [rotMθ'_apply, EuclideanSpace.single_apply, ↓reduceIte,
      show (0 : Fin 2) ≠ 1 from by decide, hpbar_def]
    ring
  · -- (1, 1): rotMφφ
    refine ⟨rotMφφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMφφ_norm_le_one _ _, ?_⟩
    let θ := x.ofLp 0; let φ := x.ofLp 1
    unfold nth_partial
    show (fderiv ℝ (fun y => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) x) (EuclideanSpace.single 1 1) = ⟪rotMφφ θ φ S, w⟫
    rw [congrArg (fderiv ℝ · x) (funext (fderiv_rotM_inner_e1 S w))]
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφ_outer S x)]
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    rw [show fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x = rotMφ' pbar S from
      (hpbar ▸ HasFDerivAt.rotMφ_outer pbar S).fderiv]
    congr 1; ext i
    simp only [rotMφ'_apply, EuclideanSpace.single_apply, ↓reduceIte,
      show (0 : Fin 2) ≠ 1 from by decide, hpbar_def]
    ring

/-!
## Main theorems
-/

/- [SY25] Lemma 19 (outer part) -/
theorem second_partial_inner_rotM_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) (i j : Fin 2) (y : ℝ²) :
    |(fderiv ℝ (fun z => (fderiv ℝ (rotproj_outer_unit S w) z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single j 1)| ≤ 1 := by
  by_cases hS : ‖S‖ = 0
  · have hzero : rotproj_outer_unit S w = 0 := by ext y; simp [rotproj_outer_unit, hS]
    simp only [hzero, fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply]; norm_num
  · show |nth_partial j (nth_partial i (rotproj_outer_unit S w)) y| ≤ 1
    let f : E 2 → ℝ := fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫
    have hfun : rotproj_outer_unit S w = ‖S‖⁻¹ • f := by
      ext z; simp [smul_eq_mul, div_eq_inv_mul, rotproj_outer_unit, f]
    have hf_smooth : ContDiff ℝ ⊤ f := by
      apply ContDiff.inner ℝ _ contDiff_const
      rw [contDiff_piLp]; intro k
      simp only [rotM, rotM_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> fun_prop
    have hf_diff : Differentiable ℝ f := hf_smooth.differentiable WithTop.top_ne_zero
    have hg : ContDiff ℝ ⊤ (nth_partial i f) := by
      unfold nth_partial
      exact hf_smooth.fderiv_right le_top |>.clm_apply contDiff_const
    have hg_diff : Differentiable ℝ (nth_partial i f) := hg.differentiable WithTop.top_ne_zero
    have hpartial_smul : nth_partial i (‖S‖⁻¹ • f) = ‖S‖⁻¹ • nth_partial i f :=
      funext fun z => nth_partial_const_smul i _ _ z (hf_diff z)
    have hpartial_smul2 : nth_partial j (‖S‖⁻¹ • nth_partial i f) = ‖S‖⁻¹ • nth_partial j (nth_partial i f) :=
      funext fun z => nth_partial_const_smul j _ _ z (hg_diff z)
    have hscale : nth_partial j (nth_partial i (rotproj_outer_unit S w)) y =
        nth_partial j (nth_partial i f) y / ‖S‖ := by
      rw [hfun, hpartial_smul, hpartial_smul2]
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hscale]
    obtain ⟨A, hAnorm, hAeq⟩ := second_partial_rotM_outer_eq S w y j i
    rw [hAeq]
    exact inner_bound_helper A S w w_unit hAnorm

theorem rotation_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_outer_unit S w) := fun x i j =>
  second_partial_inner_rotM_outer S w_unit j i x

end GlobalTheorem
