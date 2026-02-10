/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationPartials.SecondPartialOuter
import Noperthedron.Global.RotationPartials.Rotproj
import Noperthedron.Global.FDerivHelpers

/-!
# Second Partial Inner Lemmas

This file contains:
- **`second_partial_inner_rotM_inner`** (9 cases)
- **`rotation_partials_bounded`** (the main theorem from [SY25] Lemma 19)

Helper lemmas `comp_norm_le_one`, `neg_comp_norm_le_one`, `inner_bound_helper`, `fderiv_inner_const`
are imported from SecondPartialHelpers.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## Private lemma: second partials as inner products (inner case, 9 cases)

The second partial derivatives of rotproj_inner S w equal ⟪A S, w⟫
where A is a composition of rotR/rotR' with rotM/rotMθ/rotMφ/rotMθθ/rotMθφ/rotMφφ,
all with ‖A‖ ≤ 1.

Variables: x 0 = α, x 1 = θ, x 2 = φ (note: rotprojRM takes θ φ α)
rotproj_inner S w x = ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫
                    = ⟪rotR (x 0) (rotM (x 1) (x 2) S), w⟫

The A[i,j] table:
| i\j |    0                    |    1                  |    2                  |
|-----|-------------------------|-----------------------|-----------------------|
|  0  | -(rotR α ∘L rotM θ φ)   | rotR' α ∘L rotMθ θ φ  | rotR' α ∘L rotMφ θ φ  |
|  1  | rotR' α ∘L rotMθ θ φ    | rotR α ∘L rotMθθ θ φ  | rotR α ∘L rotMθφ θ φ  |
|  2  | rotR' α ∘L rotMφ θ φ    | rotR α ∘L rotMθφ θ φ  | rotR α ∘L rotMφφ θ φ  |
-/

set_option maxHeartbeats 400000 in
private lemma second_partial_rotM_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j : Fin 3) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (rotproj_inner S w)) x = ⟪A S, w⟫ := by
  let α := x.ofLp 0; let θ := x.ofLp 1; let φ := x.ofLp 2
  fin_cases i <;> fin_cases j
  · -- (0, 0): ∂²/∂α² → -(rotR α ∘L rotM θ φ)
    refine ⟨-(rotR α ∘L rotM θ φ), ?_, ?_⟩
    · exact neg_comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (le_of_eq (Bounding.rotM_norm_one θ φ))
    · show nth_partial 0 (nth_partial 0 (rotproj_inner S w)) x = ⟪(-(rotR α ∘L rotM θ φ)) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e0 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotM S x),
        fderiv_rotR'_rotM_in_e0 S x α θ φ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply, inner_neg_left]
  · -- (0, 1): ∂²/∂α∂θ → rotR' α ∘L rotMθ θ φ
    refine ⟨rotR' α ∘L rotMθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMθ_norm_le_one θ φ)
    · show nth_partial 0 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMθ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e1 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθ S x),
        fderiv_rotR_any_M_in_e0 S x rotMθ (differentiableAt_rotR_rotMθ S x)]
      rfl
  · -- (0, 2): ∂²/∂α∂φ → rotR' α ∘L rotMφ θ φ
    refine ⟨rotR' α ∘L rotMφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMφ_norm_le_one θ φ)
    · show nth_partial 0 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMφ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e2 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMφ S x),
        fderiv_rotR_any_M_in_e0 S x rotMφ (differentiableAt_rotR_rotMφ S x)]
      rfl
  · -- (1, 0): ∂²/∂θ∂α → rotR' α ∘L rotMθ θ φ (same as (0,1))
    refine ⟨rotR' α ∘L rotMθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMθ_norm_le_one θ φ)
    · show nth_partial 1 (nth_partial 0 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMθ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e0 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotM S x),
        fderiv_rotR'_rotM_in_e1 S x α θ φ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (1, 1): ∂²/∂θ² → rotR α ∘L rotMθθ θ φ
    refine ⟨rotR α ∘L rotMθθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθθ_norm_le_one θ φ)
    · show nth_partial 1 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθθ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e1 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθ S x),
        fderiv_rotR_rotMθ_in_e1 S x]
      rfl
  · -- (1, 2): ∂²/∂θ∂φ → rotR α ∘L rotMθφ θ φ
    refine ⟨rotR α ∘L rotMθφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθφ_norm_le_one θ φ)
    · show nth_partial 1 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθφ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e2 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMφ S x),
        fderiv_rotR_rotMφ_in_e1 S x]
      rfl
  · -- (2, 0): ∂²/∂φ∂α → rotR' α ∘L rotMφ θ φ (same as (0,2))
    refine ⟨rotR' α ∘L rotMφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMφ_norm_le_one θ φ)
    · show nth_partial 2 (nth_partial 0 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMφ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e0 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotM S x),
        fderiv_rotR'_rotM_in_e2 S x α θ φ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (2, 1): ∂²/∂φ∂θ → rotR α ∘L rotMθφ θ φ (same as (1,2))
    refine ⟨rotR α ∘L rotMθφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθφ_norm_le_one θ φ)
    · show nth_partial 2 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθφ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e1 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθ S x),
        fderiv_rotR_rotMθ_in_e2 S x]
      rfl
  · -- (2, 2): ∂²/∂φ² → rotR α ∘L rotMφφ θ φ
    refine ⟨rotR α ∘L rotMφφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMφφ_norm_le_one θ φ)
    · show nth_partial 2 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMφφ θ φ) S, w⟫
      unfold nth_partial
      rw [congrArg (fderiv ℝ · x) (funext fun y =>
        fderiv_rotproj_inner_in_e2 S w y (differentiableAt_rotR_rotM S y))]
      rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMφ S x),
        fderiv_rotR_rotMφ_in_e2 S x]
      rfl

/-!
## Main theorems
-/

/- [SY25] Lemma 19 (inner part) -/
theorem second_partial_inner_rotM_inner (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) (i j : Fin 3) (y : ℝ³) :
    |(fderiv ℝ (fun z => (fderiv ℝ (rotproj_inner_unit S w) z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single j 1)| ≤ 1 := by
  change |nth_partial j (nth_partial i (rotproj_inner_unit S w)) y| ≤ 1
  have hf_smooth : ContDiff ℝ 2 (rotproj_inner S w) := by
    change ContDiff ℝ 2 (fun x : ℝ³ => ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫)
    simp [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
    fun_prop
  have hf_diff : Differentiable ℝ (rotproj_inner S w) :=
    hf_smooth.differentiable (by decide)
  have hg_diff : Differentiable ℝ (nth_partial i (rotproj_inner S w)) :=
    (hf_smooth.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
      contDiff_const).differentiable (by decide)
  have hscale : nth_partial j (nth_partial i (rotproj_inner_unit S w)) y =
      nth_partial j (nth_partial i (rotproj_inner S w)) y / ‖S‖ := by
    simpa [rotproj_inner_unit_eq] using
      nth_partial_nth_partial_div_const j i (rotproj_inner S w) ‖S‖ y
        (Differentiable.rotproj_inner S w) hg_diff
  obtain ⟨A, hAnorm, hAeq⟩ := second_partial_rotM_inner_eq S w y j i
  simpa [hscale, hAeq] using inner_bound_helper A S w w_unit hAnorm

/- [SY25] Lemma 19 -/
theorem rotation_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_inner_unit S w) := fun x i j =>
  second_partial_inner_rotM_inner S w_unit j i x

end GlobalTheorem
