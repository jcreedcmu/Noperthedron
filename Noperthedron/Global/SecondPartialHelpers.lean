/-
Helper lemmas for second partial derivative computations in Global.lean.

These lemmas factor out repeated DifferentiableAt proofs and first partial
computations to reduce heartbeat usage in second_partial_inner_rotM_inner.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
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

end GlobalTheorem
