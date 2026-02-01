/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Noperthedron.RotationDerivs
import Noperthedron.Global.SecondPartialHelpers

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
-- Note: Linter reports false positives about seq focus and unused/unreachable tactics
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
lemma HasDerivAt_rotR' (α : ℝ) (v : ℝ²) :
    HasDerivAt (rotR' · v) (-(rotR α v)) α := by
  -- rotR' α v = !₂[-sin α * v 0 - cos α * v 1, cos α * v 0 - sin α * v 1]
  -- d/dα = !₂[-cos α * v 0 + sin α * v 1, -sin α * v 0 - cos α * v 1]
  --      = -!₂[cos α * v 0 - sin α * v 1, sin α * v 0 + cos α * v 1] = -rotR α v
  have h_f : (rotR' · v) = (fun α' => !₂[-Real.sin α' * v 0 - Real.cos α' * v 1,
      Real.cos α' * v 0 - Real.sin α' * v 1]) := by
    ext α' i
    fin_cases i <;> simp [rotR', rotR'_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : -(rotR α v) = !₂[-Real.cos α * v 0 + Real.sin α * v 1,
      -Real.sin α * v 0 - Real.cos α * v 1] := by
    ext i
    fin_cases i <;> simp [rotR, rotR_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']
  refine hasDerivAt_lp2 ?_ ?_
  · -- Component 0: d/dα(-sin α * v 0 - cos α * v 1) = -cos α * v 0 + sin α * v 1
    have h1 : HasDerivAt (fun x => -Real.sin x * v.ofLp 0) (-Real.cos α * v.ofLp 0) α := by
      have := (Real.hasDerivAt_sin α).neg.mul_const (v.ofLp 0)
      convert this using 2 <;> ring
    have h2 : HasDerivAt (fun x => -Real.cos x * v.ofLp 1) (Real.sin α * v.ofLp 1) α := by
      have := (Real.hasDerivAt_cos α).neg.mul_const (v.ofLp 1)
      convert this using 2 <;> ring
    convert h1.add h2 using 1 <;> first | (funext x; simp only [Pi.add_apply]; ring) | ring
  · -- Component 1: d/dα(cos α * v 0 - sin α * v 1) = -sin α * v 0 - cos α * v 1
    have h1 : HasDerivAt (fun x => Real.cos x * v.ofLp 0) (-Real.sin α * v.ofLp 0) α := by
      have := (Real.hasDerivAt_cos α).mul_const (v.ofLp 0)
      convert this using 2 <;> ring
    have h2 : HasDerivAt (fun x => -Real.sin x * v.ofLp 1) (-Real.cos α * v.ofLp 1) α := by
      have := (Real.hasDerivAt_sin α).neg.mul_const (v.ofLp 1)
      convert this using 2 <;> ring
    convert h1.add h2 using 1 <;> first | (funext x; simp only [Pi.add_apply]; ring) | ring

/-- fderiv of rotR with any M in direction e₀ gives rotR' -/
lemma fderiv_rotR_any_M_in_e0 (S : Euc(3)) (y : E 3) (M : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 := fun t => coord_e0_same y t
  have h1 := coord_e0_at1 y
  have h2 := coord_e0_at2 y
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S))
      (rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 0 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 0 1).ofLp 0) (M ((y + t • EuclideanSpace.single 0 1).ofLp 1) ((y + t • EuclideanSpace.single 0 1).ofLp 2) S) =
        rotR (y.ofLp 0 + t) (M (y.ofLp 1) (y.ofLp 2) S) := by intro t; rw [h0, h1, h2]
    simp_rw [hsimp]
    have hrotR : HasDerivAt (fun α => rotR α (M (y.ofLp 1) (y.ofLp 2) S)) (rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 0) := HasDerivAt_rotR _ _
    have hid : HasDerivAt (fun t : ℝ => y.ofLp 0 + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add (y.ofLp 0)
    have hrotR' : HasDerivAt (fun α => rotR α (M (y.ofLp 1) (y.ofLp 2) S)) (rotR' (y.ofLp 0 + 0) (M (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 0 + 0) := by simp only [add_zero]; exact hrotR
    have hcomp := hrotR'.scomp 0 hid
    simp only [one_smul, add_zero] at hcomp
    have heq_fun : ((fun α ↦ rotR α (M (y.ofLp 1) (y.ofLp 2) S)) ∘ HAdd.hAdd (y.ofLp 0)) = (fun t => rotR (y.ofLp 0 + t) (M (y.ofLp 1) (y.ofLp 2) S)) := by ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hcomp; exact hcomp
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
  have h0 := coord_e2_at0 y
  have h1 := coord_e2_at1 y
  have h2 := fun t => coord_e2_same y t
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 2 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 2 1).ofLp 1) ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2 + t) S) := by intro t; rw [h0, h1, h2]
    simp_rw [hsimp]
    have hrotM : HasDerivAt (fun φ => rotM (y.ofLp 1) φ S) (rotMφ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 2) :=
      hasDerivAt_rotM_φ _ _ _
    have hR : HasFDerivAt (fun v => rotR (y.ofLp 0) v) (rotR (y.ofLp 0)) (rotM (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
    have hrotM_fderiv : HasFDerivAt (fun φ : ℝ => rotM (y.ofLp 1) φ S)
        (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 2) := hrotM.hasFDerivAt
    have hcomp_inner := hR.comp (y.ofLp 2) hrotM_fderiv
    have heq_comp : (rotR (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq_comp] at hcomp_inner
    have hcomp_deriv : HasDerivAt ((fun v => rotR (y.ofLp 0) v) ∘ (fun φ => rotM (y.ofLp 1) φ S))
        (rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 2) := by
      have h := hcomp_inner.hasDerivAt (x := y.ofLp 2)
      simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
    have hid : HasDerivAt (fun t : ℝ => y.ofLp 2 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (y.ofLp 2)
    have hcomp_deriv' : HasDerivAt (fun φ => rotR (y.ofLp 0) (rotM (y.ofLp 1) φ S))
        (rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2 + 0) S)) (y.ofLp 2 + 0) := by
      simp only [add_zero] at hcomp_deriv ⊢; exact hcomp_deriv
    have hfinal := hcomp_deriv'.scomp 0 hid
    simp only [one_smul, add_zero] at hfinal
    have heq_fun : ((fun φ => rotR (y.ofLp 0) (rotM (y.ofLp 1) φ S)) ∘ HAdd.hAdd (y.ofLp 2)) =
        (fun t => rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2 + t) S)) := by ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hfinal; exact hfinal
  exact hline.lineDeriv

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₁ gives rotR ∘ rotMθ -/
lemma fderiv_rotR_rotM_in_e1 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 := coord_e1_at0 y
  have h1 := fun t => coord_e1_same y t
  have h2 := coord_e1_at2 y
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 1 1).ofLp 1) ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR (y.ofLp 0) (rotM (y.ofLp 1 + t) (y.ofLp 2) S) := by intro t; rw [h0, h1, h2]
    simp_rw [hsimp]
    have hrotM : HasDerivAt (fun θ => rotM θ (y.ofLp 2) S) (rotMθ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 1) :=
      hasDerivAt_rotM_θ _ _ _
    have hR : HasFDerivAt (fun v => rotR (y.ofLp 0) v) (rotR (y.ofLp 0)) (rotM (y.ofLp 1) (y.ofLp 2) S) :=
      ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
    have hrotM_fderiv : HasFDerivAt (fun θ : ℝ => rotM θ (y.ofLp 2) S)
        (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 1) := hrotM.hasFDerivAt
    have hcomp_inner := hR.comp (y.ofLp 1) hrotM_fderiv
    have heq_comp : (rotR (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ (y.ofLp 1) (y.ofLp 2) S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq_comp] at hcomp_inner
    have hcomp_deriv : HasDerivAt ((fun v => rotR (y.ofLp 0) v) ∘ (fun θ => rotM θ (y.ofLp 2) S))
        (rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 1) := by
      have h := hcomp_inner.hasDerivAt (x := y.ofLp 1)
      simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
    have hid : HasDerivAt (fun t : ℝ => y.ofLp 1 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (y.ofLp 1)
    have hcomp_deriv' : HasDerivAt (fun θ => rotR (y.ofLp 0) (rotM θ (y.ofLp 2) S))
        (rotR (y.ofLp 0) (rotMθ (y.ofLp 1 + 0) (y.ofLp 2) S)) (y.ofLp 1 + 0) := by
      simp only [add_zero] at hcomp_deriv ⊢; exact hcomp_deriv
    have hfinal := hcomp_deriv'.scomp 0 hid
    simp only [one_smul, add_zero] at hfinal
    have heq_fun : ((fun θ => rotR (y.ofLp 0) (rotM θ (y.ofLp 2) S)) ∘ HAdd.hAdd (y.ofLp 1)) =
        (fun t => rotR (y.ofLp 0) (rotM (y.ofLp 1 + t) (y.ofLp 2) S)) := by ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hfinal; exact hfinal
  exact hline.lineDeriv

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₀ gives -rotR -/
lemma fderiv_rotR'_rotM_in_e0 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    -(rotR α (rotM θ φ S)) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 := fun t => coord_e0_same y t
  have h1 := coord_e0_at1 y
  have h2 := coord_e0_at2 y
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (-(rotR α (rotM θ φ S))) y (EuclideanSpace.single 0 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR' ((y + t • EuclideanSpace.single 0 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 0 1).ofLp 1)
             ((y + t • EuclideanSpace.single 0 1).ofLp 2) S) =
        rotR' (y.ofLp 0 + t) (rotM (y.ofLp 1) (y.ofLp 2) S) := by
      intro t; rw [h0, h1, h2]
    simp_rw [hsimp, hθ, hφ]
    have hrotR' : HasDerivAt (fun α' => rotR' α' (rotM θ φ S))
        (-(rotR α (rotM θ φ S))) α := HasDerivAt_rotR' α (rotM θ φ S)
    have hid : HasDerivAt (fun t : ℝ => y.ofLp 0 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (y.ofLp 0)
    have hrotR'0 : HasDerivAt (fun α' => rotR' α' (rotM θ φ S))
        (-(rotR α (rotM θ φ S))) (y.ofLp 0 + 0) := by
      simp only [add_zero, hα]; exact hrotR'
    have hcomp := hrotR'0.scomp 0 hid
    simp only [one_smul] at hcomp
    have heq_fun : ((fun α' ↦ rotR' α' (rotM θ φ S)) ∘ HAdd.hAdd (y.ofLp 0)) =
        (fun t => rotR' (y.ofLp 0 + t) (rotM θ φ S)) := by
      ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hcomp
    simp only [hα] at hcomp ⊢
    exact hcomp
  exact hline.lineDeriv

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₁ gives rotR' α (rotMθ θ φ S) -/
lemma fderiv_rotR'_rotM_in_e1 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR' α (rotMθ θ φ S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 := coord_e1_at0 y
  have h1 := fun t => coord_e1_same y t
  have h2 := coord_e1_at2 y
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR' α (rotMθ θ φ S)) y (EuclideanSpace.single 1 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR' ((y + t • EuclideanSpace.single 1 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 1 1).ofLp 1)
             ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
        rotR' α (rotM (θ + t) φ S) := by
      intro t; rw [h0, h1, h2, hα, hθ, hφ, add_comm]
    simp_rw [hsimp]
    -- rotR' α is a constant linear map, so d/dt[rotR' α (rotM (θ+t) φ S)] = rotR' α (d/dt[rotM (θ+t) φ S])
    have hrotM : HasDerivAt (fun θ' => rotM θ' φ S) (rotMθ θ φ S) θ := hasDerivAt_rotM_θ θ φ S
    have hR : HasFDerivAt (fun v => rotR' α v) (rotR' α) (rotM θ φ S) := ContinuousLinearMap.hasFDerivAt (rotR' α)
    have hrotM_fderiv : HasFDerivAt (fun θ' : ℝ => rotM θ' φ S)
        (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ θ φ S)) θ := hrotM.hasFDerivAt
    have hcomp_inner := hR.comp θ hrotM_fderiv
    have heq_comp : (rotR' α).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ θ φ S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMθ θ φ S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq_comp] at hcomp_inner
    have hcomp_deriv : HasDerivAt ((fun v => rotR' α v) ∘ (fun θ' => rotM θ' φ S))
        (rotR' α (rotMθ θ φ S)) θ := by
      have h := hcomp_inner.hasDerivAt (x := θ)
      simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
    have hid : HasDerivAt (fun t : ℝ => θ + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add θ
    have hcomp_deriv' : HasDerivAt (fun θ' => rotR' α (rotM θ' φ S))
        (rotR' α (rotMθ (θ + 0) φ S)) (θ + 0) := by
      simp only [add_zero] at hcomp_deriv ⊢; exact hcomp_deriv
    have hfinal := hcomp_deriv'.scomp 0 hid
    simp only [one_smul, add_zero] at hfinal
    have heq_fun : ((fun θ' => rotR' α (rotM θ' φ S)) ∘ HAdd.hAdd θ) =
        (fun t => rotR' α (rotM (θ + t) φ S)) := by ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hfinal; exact hfinal
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
    have hsimp : ∀ t, rotR' ((y + t • EuclideanSpace.single 2 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 2 1).ofLp 1)
             ((y + t • EuclideanSpace.single 2 1).ofLp 2) S) =
        rotR' α (rotM θ (φ + t) S) := by
      intro t; rw [coord_e2_at0, coord_e2_at1, coord_e2_same, hα, hθ, hφ, add_comm]
    simp_rw [hsimp]
    have hrotM : HasDerivAt (fun φ' => rotM θ φ' S) (rotMφ θ φ S) φ := hasDerivAt_rotM_φ θ φ S
    have hR : HasFDerivAt (fun v => rotR' α v) (rotR' α) (rotM θ φ S) :=
      ContinuousLinearMap.hasFDerivAt (rotR' α)
    have hcomp := hR.comp φ hrotM.hasFDerivAt
    have heq_comp : (rotR' α).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ θ φ S)) =
        ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMφ θ φ S)) := by
      ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq_comp] at hcomp
    have hderiv := hcomp.hasDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hderiv
    exact hasDerivAt_comp_add _ _ _ hderiv
  exact hline.lineDeriv

end GlobalTheorem
