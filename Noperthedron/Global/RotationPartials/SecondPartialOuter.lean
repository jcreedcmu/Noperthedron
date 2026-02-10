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
- `outer_second_partial_A` definition and norm bound
- **`second_partial_inner_rotM_outer`** (4 cases: θθ, θφ, φθ, φφ)
- **`rotation_partials_bounded_outer`**
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
  fin_cases i <;> fin_cases j <;>
    simp [outer_second_partial_A, Bounding.rotMθθ_norm_le_one,
      Bounding.rotMθφ_norm_le_one, Bounding.rotMφφ_norm_le_one]

/-!
## Helper lemmas: partials of ⟪rotM S, w⟫ in coordinate directions
-/

private lemma outerPbar (x : E 2) : (⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ : Pose).outerParams = x := by
  ext i; fin_cases i <;> simp [Pose.outerParams]

private lemma fderiv_rotM_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) x = rotM' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotM_outer _ S).fderiv

private lemma fderiv_rotMθ_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x = rotMθ' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotMθ_outer _ S).fderiv

private lemma fderiv_rotMφ_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x = rotMφ' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotMφ_outer _ S).fderiv

private lemma fderiv_rotM_inner_e0 (S : ℝ³) (w : ℝ²) (y : E 2) :
    (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
      (EuclideanSpace.single 0 1) = ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w y _ (Differentiable.rotM_outer S y), fderiv_rotM_outer_eq S y]
  congr 1; ext i; simp [rotM'_apply, EuclideanSpace.single_apply]

private lemma fderiv_rotM_inner_e1 (S : ℝ³) (w : ℝ²) (y : E 2) :
    (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
      (EuclideanSpace.single 1 1) = ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w y _ (Differentiable.rotM_outer S y), fderiv_rotM_outer_eq S y]
  congr 1; ext i; simp [rotM'_apply, EuclideanSpace.single_apply]

private lemma fderiv_rotMθ_inner_e0 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 0 1) = ⟪rotMθθ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθ_outer S x), fderiv_rotMθ_outer_eq S x]
  congr 1; ext i; simp [rotMθ'_apply, EuclideanSpace.single_apply]

private lemma fderiv_rotMθ_inner_e1 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 1 1) = ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθ_outer S x), fderiv_rotMθ_outer_eq S x]
  congr 1; ext i; simp [rotMθ'_apply, EuclideanSpace.single_apply]

private lemma fderiv_rotMφ_inner_e0 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 0 1) = ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφ_outer S x), fderiv_rotMφ_outer_eq S x]
  congr 1; ext i; simp [rotMφ'_apply, EuclideanSpace.single_apply]

private lemma fderiv_rotMφ_inner_e1 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 1 1) = ⟪rotMφφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφ_outer S x), fderiv_rotMφ_outer_eq S x]
  congr 1; ext i; simp [rotMφ'_apply, EuclideanSpace.single_apply]

/-!
## Private lemma: second partials as inner products
-/

private lemma second_partial_rotM_outer_eq (S : ℝ³) (w : ℝ²) (x : E 2) (i j : Fin 2) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x = ⟪A S, w⟫ := by
  refine ⟨outer_second_partial_A (x.ofLp 0) (x.ofLp 1) i j,
    outer_second_partial_A_norm_le _ _ _ _, ?_⟩
  fin_cases i <;> fin_cases j <;> unfold nth_partial <;>
    simp [outer_second_partial_A, fderiv_rotM_inner_e0, fderiv_rotM_inner_e1,
      fderiv_rotMθ_inner_e0, fderiv_rotMθ_inner_e1, fderiv_rotMφ_inner_e0, fderiv_rotMφ_inner_e1]

/-!
## Main theorems
-/

/- [SY25] Lemma 19 (outer part) -/
theorem second_partial_inner_rotM_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) (i j : Fin 2) (y : ℝ²) :
    |(fderiv ℝ (fun z => (fderiv ℝ (rotproj_outer_unit S w) z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single j 1)| ≤ 1 := by
  show |nth_partial j (nth_partial i (rotproj_outer_unit S w)) y| ≤ 1
  let f : E 2 → ℝ := fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫
  have hf_smooth : ContDiff ℝ 2 f := by
    apply ContDiff.inner ℝ _ contDiff_const
    rw [contDiff_piLp]; intro k
    simp only [rotM, rotM_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> fun_prop
  have hscale : nth_partial j (nth_partial i (rotproj_outer_unit S w)) y =
      nth_partial j (nth_partial i f) y / ‖S‖ := by
    simpa using nth_partial_nth_partial_div_const i j f ‖S‖ y
      (hf_smooth.differentiable (by decide))
      ((hf_smooth.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
        contDiff_const).differentiable (by decide))
  obtain ⟨A, hAnorm, hAeq⟩ := second_partial_rotM_outer_eq S w y j i
  simpa [hscale, f, hAeq] using inner_bound_helper A S w w_unit hAnorm

theorem rotation_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_outer_unit S w) := fun x i j =>
  second_partial_inner_rotM_outer S w_unit j i x

end GlobalTheorem
