/-
Helper lemmas for second partial derivative computations in Global.lean.

These lemmas factor out repeated DifferentiableAt proofs and first partial
computations to reduce heartbeat usage in second_partial_inner_rotM_inner.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Noperthedron.RotationDerivs

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## DifferentiableAt lemmas for rotation compositions

These lemmas eliminate the repeated `rw [differentiableAt_piLp]; intro i; fin_cases i ...`
pattern that appears ~30+ times in second_partial_inner_rotM_inner.
-/

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
  fin_cases i <;> (simp [rotR, rotR_mat, rotMθ, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMφ -/
lemma differentiableAt_rotR_rotMφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMφ, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotMθ -/
lemma differentiableAt_rotR'_rotMθ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotMθ, Matrix.toEuclideanLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotMφ -/
lemma differentiableAt_rotR'_rotMφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotMφ, Matrix.toEuclideanLin_apply,
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

/-!
## Coordinate extraction lemmas

These factor out the repeated `(y + t • EuclideanSpace.single k 1).ofLp j` simplifications.
-/

/-- Coordinate extraction: direction e0, coordinate 0 (moves) -/
lemma coord_e0_same (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 + t := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    ↓reduceIte, smul_eq_mul, mul_one, add_comm]

/-- Coordinate extraction: direction e0, coordinate 1 (fixed) -/
lemma coord_e0_at1 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Coordinate extraction: direction e0, coordinate 2 (fixed) -/
lemma coord_e0_at2 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    show (2 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Coordinate extraction: direction e1, coordinate 0 (fixed) -/
lemma coord_e1_at0 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Coordinate extraction: direction e1, coordinate 1 (moves) -/
lemma coord_e1_same (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 + t := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    ↓reduceIte, smul_eq_mul, mul_one, add_comm]

/-- Coordinate extraction: direction e1, coordinate 2 (fixed) -/
lemma coord_e1_at2 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Coordinate extraction: direction e2, coordinate 0 (fixed) -/
lemma coord_e2_at0 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    show (0 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Coordinate extraction: direction e2, coordinate 1 (fixed) -/
lemma coord_e2_at1 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]

/-- Coordinate extraction: direction e2, coordinate 2 (moves) -/
lemma coord_e2_same (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 + t := by
  simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
    ↓reduceIte, smul_eq_mul, mul_one, add_comm]

/-!
## Directional fderiv lemmas for second partials

These factor out the lineDeriv_eq_fderiv + HasLineDerivAt pattern.
-/

/-- Helper for deriv → fderiv composition pattern -/
private lemma hasDerivAt_comp_add (f : ℝ → ℝ²) (f' : ℝ²) (a : ℝ) (hf : HasDerivAt f f' a) :
    HasDerivAt (fun t => f (a + t)) f' 0 := by
  have hid : HasDerivAt (fun t : ℝ => a + t) 1 0 := by simpa using (hasDerivAt_id 0).const_add a
  have hf' : HasDerivAt f f' (a + 0) := by simp only [add_zero]; exact hf
  have hcomp := hf'.scomp 0 hid
  simp only [one_smul] at hcomp
  exact hcomp

/-- fderiv of rotR' ∘ rotM in direction e1 gives rotR' ∘ rotMθ -/
private lemma fderiv_rotR'_rotM_in_e1' (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR' (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S) := by
  have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
    differentiableAt_rotR'_rotM S y
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hf_diff]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR' (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR' ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 1 1).ofLp 1) ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR' (y.ofLp 0) (rotM (y.ofLp 1 + t) (y.ofLp 2) S) := by
      intro t; rw [coord_e1_at0, coord_e1_same, coord_e1_at2, add_comm]
    simp_rw [hsimp]
    have hrotM : HasDerivAt (fun θ' => rotM θ' (y.ofLp 2) S) (rotMθ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 1) :=
      hasDerivAt_rotM_θ _ _ _
    have hR' : HasFDerivAt (fun v => rotR' (y.ofLp 0) v) (rotR' (y.ofLp 0)) (rotM (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR' (y.ofLp 0))
    have hcomp := hR'.comp (y.ofLp 1) hrotM.hasFDerivAt
    have heq : (rotR' (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq] at hcomp
    have hderiv := hcomp.hasDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hderiv
    exact hasDerivAt_comp_add _ _ _ hderiv
  exact hline.lineDeriv

/-- fderiv of rotR' ∘ rotM in direction e2 gives rotR' ∘ rotMφ -/
private lemma fderiv_rotR'_rotM_in_e2' (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR' (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S) := by
  have hf_diff := differentiableAt_rotR'_rotM S y
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hf_diff]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR' (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR' ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 2 1).ofLp 1) ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2 + t) S) := by
      intro t; rw [coord_e2_at0, coord_e2_at1, coord_e2_same, add_comm]
    simp_rw [hsimp]
    have hrotM : HasDerivAt (fun φ' => rotM (y.ofLp 1) φ' S) (rotMφ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 2) :=
      hasDerivAt_rotM_φ _ _ _
    have hR' : HasFDerivAt (fun v => rotR' (y.ofLp 0) v) (rotR' (y.ofLp 0)) (rotM (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR' (y.ofLp 0))
    have hcomp := hR'.comp (y.ofLp 2) hrotM.hasFDerivAt
    have heq : (rotR' (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq] at hcomp
    have hderiv := hcomp.hasDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hderiv
    exact hasDerivAt_comp_add _ _ _ hderiv
  exact hline.lineDeriv

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
    have hrotMθ : HasDerivAt (fun θ' => rotMθ θ' (y.ofLp 2) S) (rotMθθ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 1) :=
      hasDerivAt_rotMθ_θ _ _ _
    have hR : HasFDerivAt (fun v => rotR (y.ofLp 0) v) (rotR (y.ofLp 0)) (rotMθ (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
    have hcomp := hR.comp (y.ofLp 1) hrotMθ.hasFDerivAt
    have heq : (rotR (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθθ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR (y.ofLp 0) (rotMθθ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq] at hcomp
    have hderiv := hcomp.hasDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hderiv
    exact hasDerivAt_comp_add _ _ _ hderiv
  exact hline.lineDeriv

/-- fderiv of rotR ∘ rotMθ in direction e2 gives rotR ∘ rotMθφ -/
lemma fderiv_rotR_rotMθ_in_e2 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) := by
  have hf_diff := differentiableAt_rotR_rotMθ S y
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hf_diff]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotMθ ((y + t • EuclideanSpace.single 2 1).ofLp 1) ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2 + t) S) := by
      intro t; rw [coord_e2_at0, coord_e2_at1, coord_e2_same, add_comm]
    simp_rw [hsimp]
    have hrotMθ : HasDerivAt (fun φ' => rotMθ (y.ofLp 1) φ' S) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 2) :=
      hasDerivAt_rotMθ_φ _ _ _
    have hR : HasFDerivAt (fun v => rotR (y.ofLp 0) v) (rotR (y.ofLp 0)) (rotMθ (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
    have hcomp := hR.comp (y.ofLp 2) hrotMθ.hasFDerivAt
    have heq : (rotR (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq] at hcomp
    have hderiv := hcomp.hasDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hderiv
    exact hasDerivAt_comp_add _ _ _ hderiv
  exact hline.lineDeriv

/-- fderiv of rotR ∘ rotMφ in direction e1 gives rotR ∘ rotMθφ -/
lemma fderiv_rotR_rotMφ_in_e1 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) := by
  have hf_diff := differentiableAt_rotR_rotMφ S y
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hf_diff]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotMφ ((y + t • EuclideanSpace.single 1 1).ofLp 1) ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotMφ (y.ofLp 1 + t) (y.ofLp 2) S) := by
      intro t; rw [coord_e1_at0, coord_e1_same, coord_e1_at2, add_comm]
    simp_rw [hsimp]
    have hrotMφ : HasDerivAt (fun θ' => rotMφ θ' (y.ofLp 2) S) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 1) :=
      hasDerivAt_rotMφ_θ _ _ _
    have hR : HasFDerivAt (fun v => rotR (y.ofLp 0) v) (rotR (y.ofLp 0)) (rotMφ (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
    have hcomp := hR.comp (y.ofLp 1) hrotMφ.hasFDerivAt
    have heq : (rotR (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq] at hcomp
    have hderiv := hcomp.hasDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hderiv
    exact hasDerivAt_comp_add _ _ _ hderiv
  exact hline.lineDeriv

/-- fderiv of rotR ∘ rotMφ in direction e2 gives rotR ∘ rotMφφ -/
lemma fderiv_rotR_rotMφ_in_e2 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S) := by
  have hf_diff := differentiableAt_rotR_rotMφ S y
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hf_diff]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotMφ ((y + t • EuclideanSpace.single 2 1).ofLp 1) ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2 + t) S) := by
      intro t; rw [coord_e2_at0, coord_e2_at1, coord_e2_same, add_comm]
    simp_rw [hsimp]
    have hrotMφ : HasDerivAt (fun φ' => rotMφ (y.ofLp 1) φ' S) (rotMφφ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 2) :=
      hasDerivAt_rotMφ_φ _ _ _
    have hR : HasFDerivAt (fun v => rotR (y.ofLp 0) v) (rotR (y.ofLp 0)) (rotMφ (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
    have hcomp := hR.comp (y.ofLp 2) hrotMφ.hasFDerivAt
    have heq : (rotR (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMφφ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq] at hcomp
    have hderiv := hcomp.hasDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hderiv
    exact hasDerivAt_comp_add _ _ _ hderiv
  exact hline.lineDeriv

end GlobalTheorem
