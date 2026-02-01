/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Noperthedron.RotationDerivs
import Noperthedron.Bounding.OpNorm

/-!
# Second Partial Helper Lemmas

Helper lemmas for second partial derivative computations in Global.lean.

These lemmas factor out repeated DifferentiableAt proofs and first partial
computations to reduce heartbeat usage in second_partial_inner_rotM_inner.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## DifferentiableAt lemmas for rotation compositions

These lemmas eliminate the repeated `rw [differentiableAt_piLp]; intro i; fin_cases i ...`
pattern that appears ~30+ times in second_partial_inner_rotM_inner.
-/

/-- DifferentiableAt for rotMθ (outer, E 2) -/
lemma differentiableAt_rotMθ_outer (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMθ (z.ofLp 0) (z.ofLp 1) S) y := by
  rw [differentiableAt_piLp]; intro i
  simp only [rotMθ, rotMθ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
  fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotMφ (outer, E 2) -/
lemma differentiableAt_rotMφ_outer (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMφ (z.ofLp 0) (z.ofLp 1) S) y := by
  rw [differentiableAt_piLp]; intro i
  simp only [rotMφ, rotMφ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop

/-- DifferentiableAt for rotR ∘ rotM -/
lemma differentiableAt_rotR_rotM (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotM, rotM_mat, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotM -/
lemma differentiableAt_rotR'_rotM (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotM, rotM_mat, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMθ -/
lemma differentiableAt_rotR_rotMθ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMθ, rotMθ_mat, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMφ -/
lemma differentiableAt_rotR_rotMφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMφ, rotMφ_mat, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotMθ -/
lemma differentiableAt_rotR'_rotMθ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotMθ, rotMθ_mat, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotMφ -/
lemma differentiableAt_rotR'_rotMφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotMφ, rotMφ_mat, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-!
## Inner product fderiv helper

This lemma factors out the repeated pattern:
```
have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (e_i)
have hw := hasFDerivAt_const w y
rw [hw.fderiv] at hInner
simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
```

The result is: `fderiv (⟪f·, w⟫) y d = ⟪fderiv f y d, w⟫` when `w` is constant.
-/

/-- fderiv of inner product with constant second argument equals inner product of fderiv -/
lemma fderiv_inner_const {n : ℕ} (f : E n → ℝ²) (w : ℝ²) (y : E n) (d : E n)
    (hf : DifferentiableAt ℝ f y) :
    (fderiv ℝ (fun z => ⟪f z, w⟫) y) d = ⟪(fderiv ℝ f y) d, w⟫ := by
  have hInner := fderiv_inner_apply ℝ hf (differentiableAt_const w) d
  have hw : HasFDerivAt (fun _ : E n ↦ w) (0 : E n →L[ℝ] ℝ²) y := hasFDerivAt_const w y
  rw [hw.fderiv] at hInner
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
  exact hInner

/-- |⟪A S, w⟫ / ‖S‖| ≤ 1 when ‖A‖ ≤ 1 and ‖w‖ = 1 -/
lemma inner_bound_helper (A : ℝ³ →L[ℝ] ℝ²) (S : ℝ³) (w : ℝ²)
    (hw : ‖w‖ = 1) (hA : ‖A‖ ≤ 1) : |⟪A S, w⟫ / ‖S‖| ≤ 1 := by
  by_cases hS : ‖S‖ = 0
  · simp [hS]
  · rw [abs_div, abs_norm]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    calc |⟪A S, w⟫|
      _ ≤ ‖A S‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖S‖ * ‖w‖ := by
          apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ 1 * ‖S‖ * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (le_of_eq hw)
            (norm_nonneg _)
          positivity
      _ = ‖S‖ := by ring

/-!
## Coordinate extraction lemmas

These factor out the repeated `(y + t • EuclideanSpace.single k 1).ofLp j` simplifications.
-/

/-- Coordinate extraction: direction e_i, same coordinate (moves) -/
lemma coord_ei_same (i : Fin 3) (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 3)).ofLp i = y.ofLp i + t := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    ↓reduceIte, smul_eq_mul, mul_one, add_comm]

/-- Coordinate extraction: direction e_i, different coordinate j (fixed) -/
@[simp]
lemma coord_ei_at_other (i j : Fin 3) (hij : j ≠ i) (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 3)).ofLp j = y.ofLp j := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply, hij,
    ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Shorthand for coord_ei_same 0 -/
abbrev coord_e0_same := coord_ei_same 0
/-- Shorthand for coord_ei_same 1 -/
abbrev coord_e1_same := coord_ei_same 1
/-- Shorthand for coord_ei_same 2 -/
abbrev coord_e2_same := coord_ei_same 2

@[simp]
lemma coord_e0_at1 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (0 : Fin 3) 1 : E 3)).ofLp 1 = y.ofLp 1 :=
  coord_ei_at_other 0 1 (by decide) y t

@[simp]
lemma coord_e0_at2 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (0 : Fin 3) 1 : E 3)).ofLp 2 = y.ofLp 2 :=
  coord_ei_at_other 0 2 (by decide) y t

@[simp]
lemma coord_e1_at0 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (1 : Fin 3) 1 : E 3)).ofLp 0 = y.ofLp 0 :=
  coord_ei_at_other 1 0 (by decide) y t

@[simp]
lemma coord_e1_at2 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (1 : Fin 3) 1 : E 3)).ofLp 2 = y.ofLp 2 :=
  coord_ei_at_other 1 2 (by decide) y t

@[simp]
lemma coord_e2_at0 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (2 : Fin 3) 1 : E 3)).ofLp 0 = y.ofLp 0 :=
  coord_ei_at_other 2 0 (by decide) y t

@[simp]
lemma coord_e2_at1 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (2 : Fin 3) 1 : E 3)).ofLp 1 = y.ofLp 1 :=
  coord_ei_at_other 2 1 (by decide) y t

/-!
## Directional fderiv lemmas for second partials

These factor out the lineDeriv_eq_fderiv + HasLineDerivAt pattern.
-/

/-- Helper for deriv → fderiv composition pattern -/
lemma hasDerivAt_comp_add (f : ℝ → ℝ²) (f' : ℝ²) (a : ℝ) (hf : HasDerivAt f f' a) :
    HasDerivAt (fun t => f (a + t)) f' 0 := by
  have hid : HasDerivAt (fun t : ℝ => a + t) 1 0 := by simpa using (hasDerivAt_id 0).const_add a
  have hf' : HasDerivAt f f' (a + 0) := by simp only [add_zero]; exact hf
  simpa [one_smul] using hf'.scomp 0 hid

/-- R ∘L toSpanSingleton v = toSpanSingleton (R v) for any ContinuousLinearMap R -/
@[simp]
lemma comp_toSpanSingleton (R : ℝ² →L[ℝ] ℝ²) (v : ℝ²) :
    R ∘L ContinuousLinearMap.toSpanSingleton ℝ v = ContinuousLinearMap.toSpanSingleton ℝ (R v) := by
  ext z
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- fderiv of rotR ∘ rotMθ in direction e1 gives rotR ∘ rotMθθ -/
lemma fderiv_rotR_rotMθ_in_e1 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθθ (y.ofLp 1) (y.ofLp 2) S) := by
  have hf_diff := differentiableAt_rotR_rotMθ S y
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hf_diff]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMθθ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotMθ ((y + t • EuclideanSpace.single 1 1).ofLp 1) ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotMθ (y.ofLp 1 + t) (y.ofLp 2) S) := by
      intro t; rw [coord_e1_at0, coord_e1_same, coord_e1_at2, add_comm]
    simp_rw [hsimp]
    have hcomp := (ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp
        (y.ofLp 1) (hasDerivAt_rotMθ_θ (y.ofLp 1) (y.ofLp 2) S).hasFDerivAt
    simp only [comp_toSpanSingleton] at hcomp
    exact hasDerivAt_comp_add _ _ _ (by simpa using hcomp.hasDerivAt)
  exact hline.lineDeriv

/-- fderiv of rotR ∘ rotMθ in direction e2 gives rotR ∘ rotMθφ -/
lemma fderiv_rotR_rotMθ_in_e2 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← (differentiableAt_rotR_rotMθ S y).lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotMθ ((y + t • EuclideanSpace.single 2 1).ofLp 1) ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2 + t) S) by
      rw [coord_e2_at0, coord_e2_at1, coord_e2_same, add_comm]]
    have hcomp := (ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp
        (y.ofLp 2) (hasDerivAt_rotMθ_φ (y.ofLp 1) (y.ofLp 2) S).hasFDerivAt
    simp only [comp_toSpanSingleton] at hcomp
    exact hasDerivAt_comp_add _ _ _ (by simpa using hcomp.hasDerivAt)
  exact hline.lineDeriv

/-- fderiv of rotR ∘ rotMφ in direction e1 gives rotR ∘ rotMθφ -/
lemma fderiv_rotR_rotMφ_in_e1 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← (differentiableAt_rotR_rotMφ S y).lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotMφ ((y + t • EuclideanSpace.single 1 1).ofLp 1) ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotMφ (y.ofLp 1 + t) (y.ofLp 2) S) by
      rw [coord_e1_at0, coord_e1_same, coord_e1_at2, add_comm]]
    have hcomp := (ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp
        (y.ofLp 1) (hasDerivAt_rotMφ_θ (y.ofLp 1) (y.ofLp 2) S).hasFDerivAt
    simp only [comp_toSpanSingleton] at hcomp
    exact hasDerivAt_comp_add _ _ _ (by simpa using hcomp.hasDerivAt)
  exact hline.lineDeriv

/-- fderiv of rotR ∘ rotMφ in direction e2 gives rotR ∘ rotMφφ -/
lemma fderiv_rotR_rotMφ_in_e2 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← (differentiableAt_rotR_rotMφ S y).lineDeriv_eq_fderiv]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    simp_rw [fun t => show rotR ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotMφ ((y + t • EuclideanSpace.single 2 1).ofLp 1) ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2 + t) S) by
      rw [coord_e2_at0, coord_e2_at1, coord_e2_same, add_comm]]
    have hcomp := (ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp
        (y.ofLp 2) (hasDerivAt_rotMφ_φ (y.ofLp 1) (y.ofLp 2) S).hasFDerivAt
    simp only [comp_toSpanSingleton] at hcomp
    exact hasDerivAt_comp_add _ _ _ (by simpa using hcomp.hasDerivAt)
  exact hline.lineDeriv

/-!
## A[i,j] Table for Second Partials

This defines the operator A_{i,j}(α, θ, φ) such that
  ∂²(rotproj_inner S w)/∂x_i∂x_j = ⟪A_{i,j} S, w⟫

where x₀ = α, x₁ = θ, x₂ = φ.

The table is:
| i\j |    0                    |    1                  |    2                  |
|-----|-------------------------|-----------------------|-----------------------|
|  0  | -(rotR α ∘L rotM θ φ)   | rotR' α ∘L rotMθ θ φ  | rotR' α ∘L rotMφ θ φ  |
|  1  | rotR' α ∘L rotMθ θ φ    | rotR α ∘L rotMθθ θ φ  | rotR α ∘L rotMθφ θ φ  |
|  2  | rotR' α ∘L rotMφ θ φ    | rotR α ∘L rotMθφ θ φ  | rotR α ∘L rotMφφ θ φ  |

All have operator norm ≤ 1 since ‖rotR‖ = ‖rotR'‖ = 1 and ‖rotM*‖ ≤ 1.
-/

/-- The operator A[i,j] for second partials of the inner rotation projection.
    Returns the composition that appears in ⟪A S, w⟫. -/
noncomputable def inner_second_partial_A (α θ φ : ℝ) (i j : Fin 3) : ℝ³ →L[ℝ] ℝ² :=
  match i, j with
  | 0, 0 => -(rotR α ∘L rotM θ φ)
  | 0, 1 => rotR' α ∘L rotMθ θ φ
  | 0, 2 => rotR' α ∘L rotMφ θ φ
  | 1, 0 => rotR' α ∘L rotMθ θ φ   -- = A[0,1] by mixed partial symmetry
  | 1, 1 => rotR α ∘L rotMθθ θ φ
  | 1, 2 => rotR α ∘L rotMθφ θ φ
  | 2, 0 => rotR' α ∘L rotMφ θ φ   -- = A[0,2] by mixed partial symmetry
  | 2, 1 => rotR α ∘L rotMθφ θ φ   -- = A[1,2] by mixed partial symmetry
  | 2, 2 => rotR α ∘L rotMφφ θ φ

/-- Composition norm bound: ‖A ∘L B‖ ≤ 1 when ‖A‖ ≤ 1 and ‖B‖ ≤ 1 -/
lemma comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖A ∘L B‖ ≤ 1 :=
  calc ‖A ∘L B‖ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le A B
    _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) (by linarith)
    _ = 1 := one_mul 1

/-- Negated composition norm bound: ‖-(A ∘L B)‖ ≤ 1 when ‖A‖ ≤ 1 and ‖B‖ ≤ 1 -/
lemma neg_comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖-(A ∘L B)‖ ≤ 1 := by
  rw [norm_neg]; exact comp_norm_le_one hA hB

/-- All A[i,j] have operator norm ≤ 1. -/
lemma inner_second_partial_A_norm_le (α θ φ : ℝ) (i j : Fin 3) :
    ‖inner_second_partial_A α θ φ i j‖ ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact neg_comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (le_of_eq (Bounding.rotM_norm_one _ _))
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMθ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMθ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMθθ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMφφ_norm_le_one _ _)

end GlobalTheorem
