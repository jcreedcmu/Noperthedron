/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.Definitions

/-!
# RotM Outer HasFDerivAt Lemmas

This file contains:
- `rotM'` definition
- `Differentiable.rotM_outer`
- **`HasFDerivAt.rotM_outer`**
- `rotMθ'`, **`HasFDerivAt.rotMθ_outer`**
- `rotMφ'`, **`HasFDerivAt.rotMφ_outer`**
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private noncomputable abbrev proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
private noncomputable abbrev proj1 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1

private lemma outerParams_0 (pbar : Pose) : pbar.outerParams.ofLp 0 = pbar.θ₂ := by simp [Pose.outerParams]
private lemma outerParams_1 (pbar : Pose) : pbar.outerParams.ofLp 1 = pbar.φ₂ := by simp [Pose.outerParams]

private lemma rotMθ_apply_0 (θ φ : ℝ) (P : ℝ³) :
    (rotMθ θ φ P) 0 = -Real.cos θ * P 0 - Real.sin θ * P 1 := by
  simp [rotMθ, rotMθ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_apply_1 (θ φ : ℝ) (P : ℝ³) :
    (rotMθ θ φ P) 1 = Real.sin θ * Real.cos φ * P 0 - Real.cos θ * Real.cos φ * P 1 := by
  simp [rotMθ, rotMθ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMφ_apply_0 (θ φ : ℝ) (P : ℝ³) : (rotMφ θ φ P) 0 = 0 := by
  simp [rotMφ, rotMφ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private lemma rotMφ_apply_1 (θ φ : ℝ) (P : ℝ³) :
    (rotMφ θ φ P) 1 = Real.cos θ * Real.sin φ * P 0 + Real.sin θ * Real.sin φ * P 1 + Real.cos φ * P 2 := by
  simp [rotMφ, rotMφ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθθ_apply_0 (θ φ : ℝ) (P : ℝ³) :
    (rotMθθ θ φ P) 0 = Real.sin θ * P 0 - Real.cos θ * P 1 := by
  simp [rotMθθ, rotMθθ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθθ_apply_1 (θ φ : ℝ) (P : ℝ³) :
    (rotMθθ θ φ P) 1 = Real.cos θ * Real.cos φ * P 0 + Real.sin θ * Real.cos φ * P 1 := by
  simp [rotMθθ, rotMθθ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private lemma rotMθφ_apply_0 (θ φ : ℝ) (P : ℝ³) : (rotMθφ θ φ P) 0 = 0 := by
  simp [rotMθφ, rotMθφ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private lemma rotMθφ_apply_1 (θ φ : ℝ) (P : ℝ³) :
    (rotMθφ θ φ P) 1 = -Real.sin θ * Real.sin φ * P 0 + Real.cos θ * Real.sin φ * P 1 := by
  simp [rotMθφ, rotMθφ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private lemma rotMφφ_apply_0 (θ φ : ℝ) (P : ℝ³) : (rotMφφ θ φ P) 0 = 0 := by
  simp [rotMφφ, rotMφφ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private lemma rotMφφ_apply_1 (θ φ : ℝ) (P : ℝ³) :
    (rotMφφ θ φ P) 1 = Real.cos θ * Real.cos φ * P 0 + Real.sin θ * Real.cos φ * P 1 - Real.sin φ * P 2 := by
  simp [rotMφφ, rotMφφ_mat, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]; ring

/-- The fderiv of rotM applied to a fixed vector P, as a function of (θ, φ). -/
noncomputable
def rotM' (pbar : Pose) (P : ℝ³) : ℝ² →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMφ pbar.θ₂ pbar.φ₂ P) i
  M.toEuclideanLin.toContinuousLinearMap

lemma rotM'_apply (pbar : Pose) (P : ℝ³) (d : ℝ²) (i : Fin 2) :
    (rotM' pbar P d) i = d 0 * (rotMθ pbar.θ₂ pbar.φ₂ P) i + d 1 * (rotMφ pbar.θ₂ pbar.φ₂ P) i := by
  simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
  simp only [mul_comm (d.ofLp _)]

lemma Differentiable.rotM_outer (P : ℝ³) :
    Differentiable ℝ fun (x : ℝ²) => (rotM (x 0) (x 1)) P := by
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

lemma HasFDerivAt.rotM_outer (pbar : Pose) (P : ℝ³) :
    HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams := by
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
    PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
  have hproj1 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 1) proj1 pbar.outerParams :=
    PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 1
  have hsinθ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
      (Real.cos pbar.θ₂ • proj0) pbar.outerParams :=
    (Real.hasStrictDerivAt_sin pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0
      (outerParams_0 pbar)
  have hcosθ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
      (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams :=
    (Real.hasStrictDerivAt_cos pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0
      (outerParams_0 pbar)
  have hsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 1))
      (Real.cos pbar.φ₂ • proj1) pbar.outerParams :=
    (Real.hasStrictDerivAt_sin pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1
      (outerParams_1 pbar)
  have hcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1))
      (-(Real.sin pbar.φ₂) • proj1) pbar.outerParams :=
    (Real.hasStrictDerivAt_cos pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1
      (outerParams_1 pbar)
  intro i
  fin_cases i
  · simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotM (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun x => -Real.sin (x.ofLp 0) * P 0 + Real.cos (x.ofLp 0) * P 1 := by
      ext x; simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
    simp only [show (⟨0, zero_lt_two⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotM' pbar P) =
        ((-Real.cos pbar.θ₂ * P 0 - Real.sin pbar.θ₂ * P 1) • PiLp.proj 2 (fun _ => ℝ) 0) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, rotM'_apply, rotMθ_apply_0, rotMφ_apply_0]
      ring
    rw [hderiv]
    have hf : HasStrictFDerivAt (fun x : ℝ² => -Real.sin (x.ofLp 0) * P 0 + Real.cos (x.ofLp 0) * P 1)
        ((-Real.cos pbar.θ₂ * P 0 - Real.sin pbar.θ₂ * P 1) • proj0) pbar.outerParams := by
      have h1 := hsinθ.neg.mul_const (P 0)
      have h2 := hcosθ.mul_const (P 1)
      convert h1.add h2 using 1
      ext d
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
                 ContinuousLinearMap.neg_apply, neg_mul]
      ring
    exact hf
  · simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotM (x.ofLp 0) (x.ofLp 1)) P).ofLp (1 : Fin 2)) =
        fun x => -Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0
               - Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1
               + Real.sin (x.ofLp 1) * P 2 := by
      ext x; simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]; ring
    simp only [show (⟨1, one_lt_two⟩ : Fin 2) = (1 : Fin 2) from rfl]
    rw [hfunc]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp (rotM' pbar P) =
        (Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 0 - Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 1) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        (Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 1 + Real.cos pbar.φ₂ * P 2) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        rotM'_apply, rotMθ_apply_1, rotMφ_apply_1]
      ring
    rw [hderiv]
    have hf : HasStrictFDerivAt
        (fun x => -Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0
                - Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1
                + Real.sin (x.ofLp 1) * P 2)
        ((Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 0 - Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 1) • proj0 +
         (Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 1 + Real.cos pbar.φ₂ * P 2) • proj1)
        pbar.outerParams := by
      have hcosθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1))
          (Real.cos pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (-(Real.sin pbar.θ₂) • proj0))
          pbar.outerParams := hcosθ.mul hcosφ
      have hsinθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1))
          (Real.sin pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (Real.cos pbar.θ₂ • proj0))
          pbar.outerParams := hsinθ.mul hcosφ
      have hadd := ((hcosθcosφ.neg.mul_const (P 0)).sub (hsinθcosφ.mul_const (P 1))).add (hsinφ.mul_const (P 2))
      convert hadd using 1
      · ext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
        ring
      · ext d
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
                   ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
        ring
    exact hf

-- Fréchet derivative of rotMθ: columns are [rotMθθ, rotMθφ]
noncomputable def rotMθ' (pbar : Pose) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθθ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMθφ pbar.θ₂ pbar.φ₂ P) i
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

lemma rotMθ'_apply (pbar : Pose) (P : ℝ³) (d : ℝ²) (i : Fin 2) :
    (rotMθ' pbar P d) i = d 0 * (rotMθθ pbar.θ₂ pbar.φ₂ P) i + d 1 * (rotMθφ pbar.θ₂ pbar.φ₂ P) i := by
  simp only [rotMθ', LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
  simp only [mul_comm (d.ofLp _)]

lemma HasFDerivAt.rotMθ_outer (pbar : Pose) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMθ (x.ofLp 0) (x.ofLp 1)) P) (rotMθ' pbar P) pbar.outerParams := by
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
    PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
  have hproj1 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 1) proj1 pbar.outerParams :=
    PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 1
  have hcosθ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
      (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams :=
    (Real.hasStrictDerivAt_cos pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0
      (outerParams_0 pbar)
  have hsinθ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
      (Real.cos pbar.θ₂ • proj0) pbar.outerParams :=
    (Real.hasStrictDerivAt_sin pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0
      (outerParams_0 pbar)
  have hcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1))
      (-(Real.sin pbar.φ₂) • proj1) pbar.outerParams :=
    (Real.hasStrictDerivAt_cos pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1
      (outerParams_1 pbar)
  intro i
  fin_cases i
  · simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMθ (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun x => -Real.cos (x.ofLp 0) * P 0 - Real.sin (x.ofLp 0) * P 1 := by
      ext x; exact rotMθ_apply_0 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨0, zero_lt_two⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotMθ' pbar P) =
        ((Real.sin pbar.θ₂ * P 0 - Real.cos pbar.θ₂ * P 1) • PiLp.proj 2 (fun _ => ℝ) 0) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, rotMθ'_apply, rotMθθ_apply_0, rotMθφ_apply_0]
      ring
    rw [hderiv]
    have hf : HasStrictFDerivAt (fun x : ℝ² => -Real.cos (x.ofLp 0) * P 0 - Real.sin (x.ofLp 0) * P 1)
        ((Real.sin pbar.θ₂ * P 0 - Real.cos pbar.θ₂ * P 1) • proj0) pbar.outerParams := by
      have h1 := hcosθ.neg.mul_const (P 0)
      have h2 := hsinθ.mul_const (P 1)
      convert h1.sub h2 using 1
      ext d
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
                 ContinuousLinearMap.neg_apply, neg_mul, neg_neg]
      ring
    exact hf
  · simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMθ (x.ofLp 0) (x.ofLp 1)) P).ofLp (1 : Fin 2)) =
        fun x => Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0 -
                 Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1 := by
      ext x; exact rotMθ_apply_1 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨1, one_lt_two⟩ : Fin 2) = (1 : Fin 2) from rfl]
    rw [hfunc]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp (rotMθ' pbar P) =
        ((Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 1) • proj0 +
         (-Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 1) • proj1) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        rotMθ'_apply, rotMθθ_apply_1, rotMθφ_apply_1, proj0, proj1]
      ring
    rw [hderiv]
    have hsinθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1))
        (Real.sin pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (Real.cos pbar.θ₂ • proj0))
        pbar.outerParams := hsinθ.mul hcosφ
    have hcosθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1))
        (Real.cos pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (-(Real.sin pbar.θ₂) • proj0))
        pbar.outerParams := hcosθ.mul hcosφ
    have hadd := ((hsinθcosφ.mul_const (P 0)).sub (hcosθcosφ.mul_const (P 1)))
    convert hadd using 1
    ext d
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
               ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul,
               proj0, proj1, PiLp.proj_apply]
    ring

-- Fréchet derivative of rotMφ as a function of (θ, φ)
-- Columns: [rotMθφ, rotMφφ] (derivatives w.r.t. θ, φ respectively)
noncomputable def rotMφ' (pbar : Pose) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθφ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMφφ pbar.θ₂ pbar.φ₂ P) i
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

lemma rotMφ'_apply (pbar : Pose) (P : ℝ³) (d : ℝ²) (i : Fin 2) :
    (rotMφ' pbar P d) i = d 0 * (rotMθφ pbar.θ₂ pbar.φ₂ P) i + d 1 * (rotMφφ pbar.θ₂ pbar.φ₂ P) i := by
  simp only [rotMφ', LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
  simp only [mul_comm (d.ofLp _)]

lemma HasFDerivAt.rotMφ_outer (pbar : Pose) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMφ (x.ofLp 0) (x.ofLp 1)) P) (rotMφ' pbar P) pbar.outerParams := by
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
    PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
  have hproj1 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 1) proj1 pbar.outerParams :=
    PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 1
  have hcosθ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
      (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams :=
    (Real.hasStrictDerivAt_cos pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0
      (outerParams_0 pbar)
  have hsinθ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
      (Real.cos pbar.θ₂ • proj0) pbar.outerParams :=
    (Real.hasStrictDerivAt_sin pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0
      (outerParams_0 pbar)
  have hcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1))
      (-(Real.sin pbar.φ₂) • proj1) pbar.outerParams :=
    (Real.hasStrictDerivAt_cos pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1
      (outerParams_1 pbar)
  have hsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 1))
      (Real.cos pbar.φ₂ • proj1) pbar.outerParams :=
    (Real.hasStrictDerivAt_sin pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1
      (outerParams_1 pbar)
  intro i
  fin_cases i
  · simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMφ (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun _ => (0 : ℝ) := by
      ext x; exact rotMφ_apply_0 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨0, zero_lt_two⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotMφ' pbar P) = 0 := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.zero_apply, rotMφ'_apply, rotMθφ_apply_0, rotMφφ_apply_0]
      ring
    rw [hderiv]
    exact hasStrictFDerivAt_const 0 pbar.outerParams
  · simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMφ (x.ofLp 0) (x.ofLp 1)) P).ofLp (1 : Fin 2)) =
        fun x => Real.cos (x.ofLp 0) * Real.sin (x.ofLp 1) * P 0 +
                 Real.sin (x.ofLp 0) * Real.sin (x.ofLp 1) * P 1 +
                 Real.cos (x.ofLp 1) * P 2 := by
      ext x; exact rotMφ_apply_1 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨1, one_lt_two⟩ : Fin 2) = (1 : Fin 2) from rfl]
    rw [hfunc]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp (rotMφ' pbar P) =
        ((-Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 1) • proj0 +
         (Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 1 - Real.sin pbar.φ₂ * P 2) • proj1) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        rotMφ'_apply, rotMθφ_apply_1, rotMφφ_apply_1, proj0, proj1]
      ring
    rw [hderiv]
    have hcosθsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * Real.sin (x.ofLp 1))
        (Real.cos pbar.θ₂ • (Real.cos pbar.φ₂ • proj1) + Real.sin pbar.φ₂ • (-(Real.sin pbar.θ₂) • proj0))
        pbar.outerParams := hcosθ.mul hsinφ
    have hsinθsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * Real.sin (x.ofLp 1))
        (Real.sin pbar.θ₂ • (Real.cos pbar.φ₂ • proj1) + Real.sin pbar.φ₂ • (Real.cos pbar.θ₂ • proj0))
        pbar.outerParams := hsinθ.mul hsinφ
    have h1 : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * Real.sin (x.ofLp 1) * P 0)
        ((P 0) • (Real.cos pbar.θ₂ • (Real.cos pbar.φ₂ • proj1) + Real.sin pbar.φ₂ • (-(Real.sin pbar.θ₂) • proj0)))
        pbar.outerParams := hcosθsinφ.mul_const (P 0)
    have h2 : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * Real.sin (x.ofLp 1) * P 1)
        ((P 1) • (Real.sin pbar.θ₂ • (Real.cos pbar.φ₂ • proj1) + Real.sin pbar.φ₂ • (Real.cos pbar.θ₂ • proj0)))
        pbar.outerParams := hsinθsinφ.mul_const (P 1)
    have h3 : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1) * P 2)
        ((P 2) • (-(Real.sin pbar.φ₂) • proj1))
        pbar.outerParams := hcosφ.mul_const (P 2)
    have hadd := h1.add (h2.add h3)
    convert hadd using 1
    · ext x
      simp only [Pi.add_apply]
      ring
    · ext d
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
                 neg_mul, proj0, proj1, PiLp.proj_apply]
      ring

end GlobalTheorem
