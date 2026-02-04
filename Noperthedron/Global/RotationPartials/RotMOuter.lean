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

/-- The fderiv of rotM applied to a fixed vector P, as a function of (θ, φ). -/
noncomputable
def rotM' (pbar : Pose) (P : ℝ³) : ℝ² →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMφ pbar.θ₂ pbar.φ₂ P) i
  M.toEuclideanLin.toContinuousLinearMap

lemma Differentiable.rotM_outer (P : ℝ³) :
    Differentiable ℝ fun (x : ℝ²) => (rotM (x 0) (x 1)) P := by
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

private lemma rotM_component0 (θ φ : ℝ) (P : ℝ³) :
    (rotM θ φ P) 0 = -Real.sin θ * P 0 + Real.cos θ * P 1 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]

private lemma rotM_component1 (θ φ : ℝ) (P : ℝ³) :
    (rotM θ φ P) 1 = -Real.cos θ * Real.cos φ * P 0 - Real.sin θ * Real.cos φ * P 1 + Real.sin φ * P 2 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]
  ring

lemma HasFDerivAt.rotM_outer (pbar : Pose) (P : ℝ³) :
    HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams := by
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  intro i
  fin_cases i
  · simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotM (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun x => -Real.sin (x.ofLp 0) * P 0 + Real.cos (x.ofLp 0) * P 1 := by
      ext x
      exact rotM_component0 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotM' pbar P) =
        ((-Real.cos pbar.θ₂ * P 0 - Real.sin pbar.θ₂ * P 1) • PiLp.proj 2 (fun _ => ℝ) 0) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Fin.isValue]
      -- Expand rotMθ and rotMφ at component 0
      simp only [rotMθ, rotMφ, rotMθ_mat, rotMφ_mat, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      rw [show ![-Real.cos pbar.θ₂, -Real.sin pbar.θ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![(0 : ℝ), 0, 0] (2 : Fin 3) = 0 from rfl]
      ring
    rw [hderiv]
    let proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
    have hsin : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
        (Real.cos pbar.θ₂ • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_sin pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hcos : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_cos pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hf : HasStrictFDerivAt (fun x : ℝ² => -Real.sin (x.ofLp 0) * P 0 + Real.cos (x.ofLp 0) * P 1)
        ((-Real.cos pbar.θ₂ * P 0 - Real.sin pbar.θ₂ * P 1) • proj0)
        pbar.outerParams := by
      -- Using mul_const: HasStrictFDerivAt (fun y => c y * d) (d • c') x
      have h1 : HasStrictFDerivAt (fun x : ℝ² => -Real.sin (x.ofLp 0) * P 0)
          ((P 0) • -(Real.cos pbar.θ₂ • proj0)) pbar.outerParams :=
        hsin.neg.mul_const (P 0)
      have h2 : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * P 1)
          ((P 1) • -(Real.sin pbar.θ₂ • proj0)) pbar.outerParams := by
        have := hcos.mul_const (P 1)
        -- Need to convert P 1 • -sin • proj0 to P 1 • -(sin • proj0)
        rw [show (P 1) • -(Real.sin pbar.θ₂ • proj0) = (P 1) • -Real.sin pbar.θ₂ • proj0 by
          rw [neg_smul]]
        exact this
      have hadd := h1.add h2
      convert hadd using 1
      ext d
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
                 ContinuousLinearMap.neg_apply, neg_mul]
      ring
    exact hf
  · -- Component 1: f(θ, φ) = -cos θ cos φ * P[0] - sin θ cos φ * P[1] + sin φ * P[2]
    simp only [Fin.isValue]
    -- Rewrite function using component lemma
    have hfunc : (fun x : ℝ² => ((rotM (x.ofLp 0) (x.ofLp 1)) P).ofLp (1 : Fin 2)) =
        fun x => -Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0
               - Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1
               + Real.sin (x.ofLp 1) * P 2 := by
      ext x
      exact rotM_component1 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) from rfl]
    rw [hfunc]
    -- Derivative structure: ∂/∂θ and ∂/∂φ combined
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp (rotM' pbar P) =
        (Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 0 - Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 1) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        (Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 1 + Real.cos pbar.φ₂ * P 2) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Fin.isValue]
      simp only [rotMθ, rotMφ, rotMθ_mat, rotMφ_mat, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      rw [show ![Real.sin pbar.θ₂ * Real.cos pbar.φ₂, -Real.cos pbar.θ₂ * Real.cos pbar.φ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![Real.cos pbar.θ₂ * Real.sin pbar.φ₂, Real.sin pbar.θ₂ * Real.sin pbar.φ₂, Real.cos pbar.φ₂] (2 : Fin 3) = Real.cos pbar.φ₂ from rfl]
      ring
    rw [hderiv]
    -- Use the chain rule for both variables
    let proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    let proj1 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
    have hproj1 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 1) proj1 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 1
    -- Individual derivatives - need to prove pbar.outerParams.ofLp i = pbar.θ₂/φ₂
    have hθ : pbar.outerParams.ofLp 0 = pbar.θ₂ := by simp [Pose.outerParams]
    have hφ : pbar.outerParams.ofLp 1 = pbar.φ₂ := by simp [Pose.outerParams]
    have hsinθ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
        (Real.cos pbar.θ₂ • proj0) pbar.outerParams :=
      (Real.hasStrictDerivAt_sin pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0 hθ.symm
    have hcosθ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams :=
      (Real.hasStrictDerivAt_cos pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0 hθ.symm
    have hsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 1))
        (Real.cos pbar.φ₂ • proj1) pbar.outerParams :=
      (Real.hasStrictDerivAt_sin pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1 hφ.symm
    have hcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1))
        (-(Real.sin pbar.φ₂) • proj1) pbar.outerParams :=
      (Real.hasStrictDerivAt_cos pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1 hφ.symm
    -- The full derivative combines all terms
    -- This is complex - use convert to match the expected form
    have hf : HasStrictFDerivAt
        (fun x => -Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0
                - Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1
                + Real.sin (x.ofLp 1) * P 2)
        ((Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 0 - Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 1) • proj0 +
         (Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 1 + Real.cos pbar.φ₂ * P 2) • proj1)
        pbar.outerParams := by
      -- Build using product rule: d(f*g) = f(x)·g' + g(x)·f'
      -- Product of cos(θ) * cos(φ)
      have hcosθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1))
          (Real.cos pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (-(Real.sin pbar.θ₂) • proj0))
          pbar.outerParams := hcosθ.mul hcosφ
      -- Product of sin(θ) * cos(φ)
      have hsinθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1))
          (Real.sin pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (Real.cos pbar.θ₂ • proj0))
          pbar.outerParams := hsinθ.mul hcosφ
      -- Combined using add/sub/mul_const
      have hadd := ((hcosθcosφ.neg.mul_const (P 0)).sub (hsinθcosφ.mul_const (P 1))).add (hsinφ.mul_const (P 2))
      convert hadd using 1
      · -- Function equality
        ext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
        ring
      · -- Derivative equality
        ext d
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

private lemma rotMθ_component0 (θ φ : ℝ) (P : ℝ³) :
    (rotMθ θ φ P) 0 = -Real.cos θ * P 0 - Real.sin θ * P 1 := by
  simp [rotMθ, rotMθ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_component1 (θ φ : ℝ) (P : ℝ³) :
    (rotMθ θ φ P) 1 = Real.sin θ * Real.cos φ * P 0 - Real.cos θ * Real.cos φ * P 1 := by
  simp [rotMθ, rotMθ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]
  ring

lemma HasFDerivAt.rotMθ_outer (pbar : Pose) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMθ (x.ofLp 0) (x.ofLp 1)) P) (rotMθ' pbar P) pbar.outerParams := by
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  intro i
  fin_cases i
  · -- Component 0: f(θ, φ) = -cos θ * P[0] - sin θ * P[1] (only depends on θ)
    simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMθ (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun x => -Real.cos (x.ofLp 0) * P 0 - Real.sin (x.ofLp 0) * P 1 := by
      ext x; exact rotMθ_component0 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    -- The derivative: d ↦ (sin θ * P[0] - cos θ * P[1]) * d[0]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotMθ' pbar P) =
        ((Real.sin pbar.θ₂ * P 0 - Real.cos pbar.θ₂ * P 1) • PiLp.proj 2 (fun _ => ℝ) 0) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotMθ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Fin.isValue]
      simp only [rotMθθ, rotMθφ, rotMθθ_mat, rotMθφ_mat, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      -- Simplify matrix entries: ![a, b, 0] 2 = 0
      rw [show ![Real.sin pbar.θ₂, -Real.cos pbar.θ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![(0 : ℝ), 0, 0] (2 : Fin 3) = 0 from rfl]
      ring
    rw [hderiv]
    let proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
    have hcos : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_cos pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hsin : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
        (Real.cos pbar.θ₂ • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_sin pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hf : HasStrictFDerivAt (fun x : ℝ² => -Real.cos (x.ofLp 0) * P 0 - Real.sin (x.ofLp 0) * P 1)
        ((Real.sin pbar.θ₂ * P 0 - Real.cos pbar.θ₂ * P 1) • proj0) pbar.outerParams := by
      have h1 : HasStrictFDerivAt (fun x : ℝ² => -Real.cos (x.ofLp 0) * P 0)
          ((P 0) • -(-(Real.sin pbar.θ₂) • proj0)) pbar.outerParams :=
        hcos.neg.mul_const (P 0)
      have h2 : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * P 1)
          ((P 1) • Real.cos pbar.θ₂ • proj0) pbar.outerParams :=
        hsin.mul_const (P 1)
      have hsub := h1.sub h2
      convert hsub using 1
      ext d
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
                 ContinuousLinearMap.neg_apply, neg_mul, neg_neg]
      ring
    exact hf
  · -- Component 1: f(θ, φ) = sin θ * cos φ * P[0] - cos θ * cos φ * P[1]
    simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMθ (x.ofLp 0) (x.ofLp 1)) P).ofLp (1 : Fin 2)) =
        fun x => Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0 -
                 Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1 := by
      ext x; exact rotMθ_component1 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) from rfl]
    rw [hfunc]
    let proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    let proj1 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
    have hproj1 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 1) proj1 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 1
    have hcosθ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_cos pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hsinθ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
        (Real.cos pbar.θ₂ • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_sin pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1))
        (-(Real.sin pbar.φ₂) • proj1) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_cos pbar.φ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj1
    -- The derivative: d ↦ (cos θ * cos φ * P[0] + sin θ * cos φ * P[1]) * d[0] +
    --                     (-sin θ * sin φ * P[0] + cos θ * sin φ * P[1]) * d[1]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp (rotMθ' pbar P) =
        ((Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 1) • proj0 +
         (-Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 1) • proj1) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotMθ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Fin.isValue]
      simp only [rotMθθ, rotMθφ, rotMθθ_mat, rotMθφ_mat, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      -- Simplify matrix entries: ![a, b, 0] 2 = 0
      rw [show ![Real.cos pbar.θ₂ * Real.cos pbar.φ₂, Real.sin pbar.θ₂ * Real.cos pbar.φ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![-Real.sin pbar.θ₂ * Real.sin pbar.φ₂, Real.cos pbar.θ₂ * Real.sin pbar.φ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      -- Unfold local let bindings proj0/proj1 before ring
      show _ = _ * proj0 d + _ * proj1 d
      simp only [proj0, proj1, PiLp.proj_apply]
      ring
    rw [hderiv]
    -- The proof follows the same pattern as component 0: product rule + chain rule
    -- for sin θ * cos φ * P 0 - cos θ * cos φ * P 1
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

-- Component lemmas for rotMφ
private lemma rotMφ_component0 (θ φ : ℝ) (P : ℝ³) :
    (rotMφ θ φ P) 0 = 0 := by
  simp [rotMφ, rotMφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]

private lemma rotMφ_component1 (θ φ : ℝ) (P : ℝ³) :
    (rotMφ θ φ P) 1 = Real.cos θ * Real.sin φ * P 0 + Real.sin θ * Real.sin φ * P 1 + Real.cos φ * P 2 := by
  simp [rotMφ, rotMφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]
  ring

lemma HasFDerivAt.rotMφ_outer (pbar : Pose) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMφ (x.ofLp 0) (x.ofLp 1)) P) (rotMφ' pbar P) pbar.outerParams := by
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  intro i
  fin_cases i
  · -- Component 0: f(θ, φ) = 0 (constant)
    simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMφ (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun _ => (0 : ℝ) := by
      ext x; exact rotMφ_component0 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    -- Derivative of constant is 0
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotMφ' pbar P) = 0 := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.zero_apply]
      simp only [rotMφ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
      simp only [rotMθφ, rotMφφ, rotMθφ_mat, rotMφφ_mat, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.of_apply, Fin.isValue]
      -- The first row of both rotMθφ and rotMφφ matrices is all zeros
      rw [show ![0, 0, (0 : ℝ)] (1 : Fin 3) = 0 from rfl]
      rw [show ![0, 0, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      ring
    rw [hderiv]
    exact hasStrictFDerivAt_const 0 pbar.outerParams
  · -- Component 1: f(θ, φ) = cos θ * sin φ * P[0] + sin θ * sin φ * P[1] + cos φ * P[2]
    simp only [Fin.isValue]
    have hfunc : (fun x : ℝ² => ((rotMφ (x.ofLp 0) (x.ofLp 1)) P).ofLp (1 : Fin 2)) =
        fun x => Real.cos (x.ofLp 0) * Real.sin (x.ofLp 1) * P 0 +
                 Real.sin (x.ofLp 0) * Real.sin (x.ofLp 1) * P 1 +
                 Real.cos (x.ofLp 1) * P 2 := by
      ext x; exact rotMφ_component1 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) from rfl]
    rw [hfunc]
    let proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    let proj1 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
    have hproj1 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 1) proj1 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 1
    have hcosθ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_cos pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hsinθ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
        (Real.cos pbar.θ₂ • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_sin pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1))
        (-(Real.sin pbar.φ₂) • proj1) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_cos pbar.φ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj1
    have hsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 1))
        (Real.cos pbar.φ₂ • proj1) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_sin pbar.φ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj1
    -- The derivative: d ↦ (-sin θ * sin φ * P[0] + cos θ * sin φ * P[1]) * d[0] +
    --                     (cos θ * cos φ * P[0] + sin θ * cos φ * P[1] - sin φ * P[2]) * d[1]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp (rotMφ' pbar P) =
        ((-Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 1) • proj0 +
         (Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 1 - Real.sin pbar.φ₂ * P 2) • proj1) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotMφ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
      simp only [rotMθφ, rotMφφ, rotMθφ_mat, rotMφφ_mat, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      rw [show ![-Real.sin pbar.θ₂ * Real.sin pbar.φ₂, Real.cos pbar.θ₂ * Real.sin pbar.φ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![Real.cos pbar.θ₂ * Real.cos pbar.φ₂, Real.sin pbar.θ₂ * Real.cos pbar.φ₂, -Real.sin pbar.φ₂] (2 : Fin 3) = -Real.sin pbar.φ₂ from rfl]
      show _ = _ * proj0 d + _ * proj1 d
      simp only [proj0, proj1, PiLp.proj_apply]
      ring
    rw [hderiv]
    -- Products: cos θ * sin φ, sin θ * sin φ, cos φ
    have hcosθsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * Real.sin (x.ofLp 1))
        (Real.cos pbar.θ₂ • (Real.cos pbar.φ₂ • proj1) + Real.sin pbar.φ₂ • (-(Real.sin pbar.θ₂) • proj0))
        pbar.outerParams := hcosθ.mul hsinφ
    have hsinθsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * Real.sin (x.ofLp 1))
        (Real.sin pbar.θ₂ • (Real.cos pbar.φ₂ • proj1) + Real.sin pbar.φ₂ • (Real.cos pbar.θ₂ • proj0))
        pbar.outerParams := hsinθ.mul hsinφ
    -- Build the full derivative
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
    · -- Function equality
      ext x
      simp only [Pi.add_apply]
      ring
    · -- Derivative equality
      ext d
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
                 neg_mul, proj0, proj1, PiLp.proj_apply]
      ring

end GlobalTheorem
