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

private lemma second_partial_col0 (S : ℝ³) (w : ℝ²) (x : E 3) (i : Fin 3) :
    nth_partial i (nth_partial 0 (rotproj_inner S w)) x =
    ⟪(fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) x)
      (EuclideanSpace.single i 1), w⟫ := by
  rw [nth_partial_rotproj_inner_e0 S w]; unfold nth_partial
  exact fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotM S x)

private lemma second_partial_col1 (S : ℝ³) (w : ℝ²) (x : E 3) (i : Fin 3) :
    nth_partial i (nth_partial 1 (rotproj_inner S w)) x =
    ⟪(fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) x)
      (EuclideanSpace.single i 1), w⟫ := by
  rw [nth_partial_rotproj_inner_e1 S w]; unfold nth_partial
  exact fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθ S x)

private lemma second_partial_col2 (S : ℝ³) (w : ℝ²) (x : E 3) (i : Fin 3) :
    nth_partial i (nth_partial 2 (rotproj_inner S w)) x =
    ⟪(fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) x)
      (EuclideanSpace.single i 1), w⟫ := by
  rw [nth_partial_rotproj_inner_e2 S w]; unfold nth_partial
  exact fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMφ S x)

/-- The second partials of `rotproj_inner` are given pointwise by the
`inner_second_partial_A` table. -/
theorem second_partial_rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j : Fin 3) :
    nth_partial i (nth_partial j (rotproj_inner S w)) x =
      ⟪inner_second_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j S, w⟫ := by
  fin_cases i <;> fin_cases j
  · -- (0, 0): -(rotR α ∘L rotM θ φ)
    show nth_partial 0 (nth_partial 0 _) x = _
    rw [second_partial_col0 S w x,
      fderiv_rotR'_rotM_in_e0 S x _ _ _ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
    simp only [inner_second_partial_A, neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, inner_neg_left]
  · -- (0, 1): rotR' α ∘L rotMθ θ φ
    show nth_partial 0 (nth_partial 1 _) x = _
    rw [second_partial_col1 S w x,
      fderiv_rotR_any_M_in_e0 S x rotMθ (differentiableAt_rotR_rotMθ S x)]; rfl
  · -- (0, 2): rotR' α ∘L rotMφ θ φ
    show nth_partial 0 (nth_partial 2 _) x = _
    rw [second_partial_col2 S w x,
      fderiv_rotR_any_M_in_e0 S x rotMφ (differentiableAt_rotR_rotMφ S x)]; rfl
  · -- (1, 0): rotR' α ∘L rotMθ θ φ
    show nth_partial 1 (nth_partial 0 _) x = _
    rw [second_partial_col0 S w x,
      fderiv_rotR'_rotM_in_e1 S x _ _ _ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
    simp only [inner_second_partial_A, ContinuousLinearMap.coe_comp, Function.comp_apply]
  · -- (1, 1): rotR α ∘L rotMθθ θ φ
    show nth_partial 1 (nth_partial 1 _) x = _
    rw [second_partial_col1 S w x, fderiv_rotR_rotMθ_in_e1 S x]; rfl
  · -- (1, 2): rotR α ∘L rotMθφ θ φ
    show nth_partial 1 (nth_partial 2 _) x = _
    rw [second_partial_col2 S w x, fderiv_rotR_rotMφ_in_e1 S x]; rfl
  · -- (2, 0): rotR' α ∘L rotMφ θ φ
    show nth_partial 2 (nth_partial 0 _) x = _
    rw [second_partial_col0 S w x,
      fderiv_rotR'_rotM_in_e2 S x _ _ _ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
    simp only [inner_second_partial_A, ContinuousLinearMap.coe_comp, Function.comp_apply]
  · -- (2, 1): rotR α ∘L rotMθφ θ φ
    show nth_partial 2 (nth_partial 1 _) x = _
    rw [second_partial_col1 S w x, fderiv_rotR_rotMθ_in_e2 S x]; rfl
  · -- (2, 2): rotR α ∘L rotMφφ θ φ
    show nth_partial 2 (nth_partial 2 _) x = _
    rw [second_partial_col2 S w x, fderiv_rotR_rotMφ_in_e2 S x]; rfl

/-- Function-level form of `second_partial_rotproj_inner_eq`. -/
theorem nth_partial_nth_partial_rotproj_inner (S : ℝ³) (w : ℝ²) (i j : Fin 3) :
    nth_partial i (nth_partial j (rotproj_inner S w)) =
      fun y => ⟪inner_second_partial_A (y.ofLp 0) (y.ofLp 1) (y.ofLp 2) i j S, w⟫ :=
  funext fun y => second_partial_rotproj_inner_eq S w y i j

private lemma second_partial_rotM_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j : Fin 3) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (rotproj_inner S w)) x = ⟪A S, w⟫ :=
  ⟨inner_second_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j,
    inner_second_partial_A_norm_le _ _ _ i j,
    second_partial_rotproj_inner_eq S w x i j⟩

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
  have hg_diff : Differentiable ℝ (nth_partial i (rotproj_inner S w)) :=
    (hf_smooth.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
      contDiff_const).differentiable (by decide)
  have hscale : nth_partial j (nth_partial i (rotproj_inner_unit S w)) y =
      nth_partial j (nth_partial i (rotproj_inner S w)) y / ‖S‖ := by
    exact nth_partial_nth_partial_div_const i j (rotproj_inner S w) ‖S‖ y
      (Differentiable.rotproj_inner S w) hg_diff
  obtain ⟨A, hAnorm, hAeq⟩ := second_partial_rotM_inner_eq S w y j i
  simpa [hscale, hAeq] using inner_bound_helper A S w w_unit hAnorm

/- [SY25] Lemma 19 -/
theorem rotation_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_inner_unit S w) := fun x i j =>
  second_partial_inner_rotM_inner S w_unit j i x

/-!
## Third partials as inner products (27 cases)

Differentiating the `inner_second_partial_A` table once more: each column of the
table is `y ↦ (±) X (y 0) (N (y 1) (y 2) S)` with `X ∈ {rotR, rotR'}` and `N` in the
M-family, so the generic direction lemmas `fderiv_rotR_any_M_in_e0`,
`fderiv_rotR'_any_M_in_e0`, `fderiv_head_family_in_e1/e2` cover every case.
-/

private lemma nth_partial_neg (f : E 3 → ℝ) (i : Fin 3) (x : E 3) :
    nth_partial i (fun y => -(f y)) x = -(nth_partial i f x) := by
  show fderiv ℝ (-f) x (EuclideanSpace.single i 1) = -(fderiv ℝ f x (EuclideanSpace.single i 1))
  rw [fderiv_neg]
  simp only [neg_apply]

theorem third_partial_rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j k : Fin 3) :
    nth_partial i (nth_partial j (nth_partial k (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j k S, w⟫ := by
  have hneg00 : (fun y : E 3 =>
        ⟪inner_second_partial_A (y.ofLp 0) (y.ofLp 1) (y.ofLp 2) 0 0 S, w⟫)
      = fun y => -⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
    funext y
    simp only [inner_second_partial_A, neg_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
  fin_cases j <;> fin_cases k
  · -- column (0,0): A₂ = -(rotR ∘L rotM)
    show nth_partial i (nth_partial 0 (nth_partial 0 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 0 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 0 0, hneg00, nth_partial_neg]
    show -(nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫) x) = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotM S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR_any_M_in_e0 S x rotM (differentiableAt_rotR_rotM S x)]
      simp only [inner_third_partial_A, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
    · rw [fderiv_head_family_in_e1 S x rotR rotM _ (differentiableAt_rotR_rotM S x)
        (hasDerivAt_rotM_θ (x.ofLp 1) (x.ofLp 2) S)]
      simp only [inner_third_partial_A, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
    · rw [fderiv_head_family_in_e2 S x rotR rotM _ (differentiableAt_rotR_rotM S x)
        (hasDerivAt_rotM_φ (x.ofLp 1) (x.ofLp 2) S)]
      simp only [inner_third_partial_A, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
  · -- column (0,1): A₂ = rotR' ∘L rotMθ
    show nth_partial i (nth_partial 0 (nth_partial 1 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 0 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 0 1]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotMθ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR'_any_M_in_e0 S x rotMθ (differentiableAt_rotR'_rotMθ S x)]
      simp only [inner_third_partial_A, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
    · rw [fderiv_head_family_in_e1 S x rotR' rotMθ _ (differentiableAt_rotR'_rotMθ S x)
        (hasDerivAt_rotMθ_θ (x.ofLp 1) (x.ofLp 2) S)]; rfl
    · rw [fderiv_head_family_in_e2 S x rotR' rotMθ _ (differentiableAt_rotR'_rotMθ S x)
        (hasDerivAt_rotMθ_φ (x.ofLp 1) (x.ofLp 2) S)]; rfl
  · -- column (0,2): A₂ = rotR' ∘L rotMφ
    show nth_partial i (nth_partial 0 (nth_partial 2 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 0 2 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 0 2]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotMφ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR'_any_M_in_e0 S x rotMφ (differentiableAt_rotR'_rotMφ S x)]
      simp only [inner_third_partial_A, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
    · rw [fderiv_head_family_in_e1 S x rotR' rotMφ _ (differentiableAt_rotR'_rotMφ S x)
        (hasDerivAt_rotMφ_θ (x.ofLp 1) (x.ofLp 2) S)]; rfl
    · rw [fderiv_head_family_in_e2 S x rotR' rotMφ _ (differentiableAt_rotR'_rotMφ S x)
        (hasDerivAt_rotMφ_φ (x.ofLp 1) (x.ofLp 2) S)]; rfl
  · -- column (1,0): A₂ = rotR' ∘L rotMθ (mixed-partial symmetry)
    show nth_partial i (nth_partial 1 (nth_partial 0 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 1 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 1 0]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotMθ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR'_any_M_in_e0 S x rotMθ (differentiableAt_rotR'_rotMθ S x)]
      simp only [inner_third_partial_A, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
    · rw [fderiv_head_family_in_e1 S x rotR' rotMθ _ (differentiableAt_rotR'_rotMθ S x)
        (hasDerivAt_rotMθ_θ (x.ofLp 1) (x.ofLp 2) S)]; rfl
    · rw [fderiv_head_family_in_e2 S x rotR' rotMθ _ (differentiableAt_rotR'_rotMθ S x)
        (hasDerivAt_rotMθ_φ (x.ofLp 1) (x.ofLp 2) S)]; rfl
  · -- column (1,1): A₂ = rotR ∘L rotMθθ
    show nth_partial i (nth_partial 1 (nth_partial 1 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 1 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 1 1]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMθθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθθ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR_any_M_in_e0 S x rotMθθ (differentiableAt_rotR_rotMθθ S x)]; rfl
    · rw [fderiv_head_family_in_e1 S x rotR rotMθθ _ (differentiableAt_rotR_rotMθθ S x)
        (hasDerivAt_rotMθθ_θ (x.ofLp 1) (x.ofLp 2) S)]
      simp only [inner_third_partial_A, map_neg, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
    · rw [fderiv_head_family_in_e2 S x rotR rotMθθ _ (differentiableAt_rotR_rotMθθ S x)
        (hasDerivAt_rotMθθ_φ (x.ofLp 1) (x.ofLp 2) S)]; rfl
  · -- column (1,2): A₂ = rotR ∘L rotMθφ
    show nth_partial i (nth_partial 1 (nth_partial 2 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 1 2 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 1 2]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθφ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR_any_M_in_e0 S x rotMθφ (differentiableAt_rotR_rotMθφ S x)]; rfl
    · rw [fderiv_head_family_in_e1 S x rotR rotMθφ _ (differentiableAt_rotR_rotMθφ S x)
        (hasDerivAt_rotMθφ_θ (x.ofLp 1) (x.ofLp 2) S)]; rfl
    · rw [fderiv_head_family_in_e2 S x rotR rotMθφ _ (differentiableAt_rotR_rotMθφ S x)
        (hasDerivAt_rotMθφ_φ (x.ofLp 1) (x.ofLp 2) S)]; rfl
  · -- column (2,0): A₂ = rotR' ∘L rotMφ (mixed-partial symmetry)
    show nth_partial i (nth_partial 2 (nth_partial 0 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 2 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 2 0]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotMφ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR'_any_M_in_e0 S x rotMφ (differentiableAt_rotR'_rotMφ S x)]
      simp only [inner_third_partial_A, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
    · rw [fderiv_head_family_in_e1 S x rotR' rotMφ _ (differentiableAt_rotR'_rotMφ S x)
        (hasDerivAt_rotMφ_θ (x.ofLp 1) (x.ofLp 2) S)]; rfl
    · rw [fderiv_head_family_in_e2 S x rotR' rotMφ _ (differentiableAt_rotR'_rotMφ S x)
        (hasDerivAt_rotMφ_φ (x.ofLp 1) (x.ofLp 2) S)]; rfl
  · -- column (2,1): A₂ = rotR ∘L rotMθφ (mixed-partial symmetry)
    show nth_partial i (nth_partial 2 (nth_partial 1 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 2 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 2 1]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθφ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR_any_M_in_e0 S x rotMθφ (differentiableAt_rotR_rotMθφ S x)]; rfl
    · rw [fderiv_head_family_in_e1 S x rotR rotMθφ _ (differentiableAt_rotR_rotMθφ S x)
        (hasDerivAt_rotMθφ_θ (x.ofLp 1) (x.ofLp 2) S)]; rfl
    · rw [fderiv_head_family_in_e2 S x rotR rotMθφ _ (differentiableAt_rotR_rotMθφ S x)
        (hasDerivAt_rotMθφ_φ (x.ofLp 1) (x.ofLp 2) S)]; rfl
  · -- column (2,2): A₂ = rotR ∘L rotMφφ
    show nth_partial i (nth_partial 2 (nth_partial 2 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 2 2 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 2 2]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    unfold nth_partial
    rw [fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMφφ S x)]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [fderiv_rotR_any_M_in_e0 S x rotMφφ (differentiableAt_rotR_rotMφφ S x)]; rfl
    · rw [fderiv_head_family_in_e1 S x rotR rotMφφ _ (differentiableAt_rotR_rotMφφ S x)
        (hasDerivAt_rotMφφ_θ (x.ofLp 1) (x.ofLp 2) S)]; rfl
    · rw [fderiv_head_family_in_e2 S x rotR rotMφφ _ (differentiableAt_rotR_rotMφφ S x)
        (hasDerivAt_rotMφφ_φ (x.ofLp 1) (x.ofLp 2) S)]
      simp only [inner_third_partial_A, map_neg, neg_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]

theorem third_partial_inner_rotM_inner (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (i j k : Fin 3) (y : ℝ³) :
    |nth_partial i (nth_partial j (nth_partial k (rotproj_inner_unit S w))) y| ≤ 1 := by
  have hf_smooth : ContDiff ℝ 3 (rotproj_inner S w) := by
    change ContDiff ℝ 3 (fun x : ℝ³ => ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫)
    simp [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
    fun_prop
  have hg_c2 : ContDiff ℝ 2 (nth_partial k (rotproj_inner S w)) :=
    hf_smooth.fderiv_right (by decide : (2 : WithTop ℕ∞) + 1 ≤ 3) |>.clm_apply contDiff_const
  have hg_diff : Differentiable ℝ (nth_partial k (rotproj_inner S w)) :=
    hg_c2.differentiable (by decide)
  have hgg_diff : Differentiable ℝ (nth_partial j (nth_partial k (rotproj_inner S w))) :=
    (hg_c2.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
      contDiff_const).differentiable (by decide)
  have hscale : nth_partial i (nth_partial j (nth_partial k (rotproj_inner_unit S w))) y =
      nth_partial i (nth_partial j (nth_partial k (rotproj_inner S w))) y / ‖S‖ :=
    nth_partial_nth_partial_nth_partial_div_const i j k (rotproj_inner S w) ‖S‖ y
      (Differentiable.rotproj_inner S w) hg_diff hgg_diff
  rw [hscale, third_partial_rotproj_inner_eq S w y i j k]
  exact inner_bound_helper _ S w w_unit (inner_third_partial_A_norm_le _ _ _ i j k)

theorem rotation_third_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    third_partials_bounded (rotproj_inner_unit S w) := fun x i j k =>
  third_partial_inner_rotM_inner S w_unit i j k x

end GlobalTheorem
