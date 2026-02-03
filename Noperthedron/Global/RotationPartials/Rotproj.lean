/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Noperthedron.RotationDerivs
import Noperthedron.Nopert
import Noperthedron.PoseInterval
import Noperthedron.Global.Definitions

/-!
# Rotproj Inner Lemmas

This file contains:
- `inner_bound_helper` (private)
- `Differentiable.rotprojRM`, `Differentiable.rotproj_inner`
- `rotproj_inner'`, `rotprojRM'` definitions
- Component lemmas: `rotR_apply_0/1`, `rotM_apply_0/1`, etc.
- **`HasFDerivAt.rotproj_inner`** (main theorem)
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- Key bound lemma for inner product with rotation matrices
private lemma inner_bound_helper (A : ℝ³ →L[ℝ] ℝ²) (S : ℝ³) (w : ℝ²)
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

lemma Differentiable.rotprojRM (S : ℝ³) :
    Differentiable ℝ fun (x : ℝ³)  ↦ (_root_.rotprojRM (x 1) (x 2) (x 0)) S := by
  unfold _root_.rotprojRM
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

@[fun_prop]
lemma Differentiable.rotproj_inner (S : ℝ³) (w : ℝ²) : Differentiable ℝ (rotproj_inner S w) :=
  Differentiable.inner ℝ (Differentiable.rotprojRM S) (by fun_prop)

/--
An explicit formula for the full derivative of rotproj_inner as a function ℝ³ → ℝ
-/
noncomputable
def rotproj_inner' (pbar : Pose) (S : ℝ³) (w : ℝ²) : ℝ³ →L[ℝ] ℝ :=
  let grad : Fin 3 → ℝ := ![
    ⟪pbar.rotR' (pbar.rotM₁ S), w⟫,
    ⟪pbar.rotR (pbar.rotM₁θ S), w⟫,
    ⟪pbar.rotR (pbar.rotM₁φ S), w⟫
  ]
  EuclideanSpace.basisFun (Fin 3) ℝ |>.toBasis.constr ℝ grad |>.toContinuousLinearMap

/--
The Fréchet derivative of `fun x => rotprojRM (x 1) (x 2) (x 0) S` at `pbar.innerParams`.
Components:
- index 0 (α): rotR' α (rotM θ φ S)
- index 1 (θ): rotR α (rotMθ θ φ S)
- index 2 (φ): rotR α (rotMφ θ φ S)
-/
noncomputable
def rotprojRM' (pbar : Pose) (S : ℝ³) : ℝ³ →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 3) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (pbar.rotR' (pbar.rotM₁ S)) i
    | 1 => (pbar.rotR (pbar.rotM₁θ S)) i
    | 2 => (pbar.rotR (pbar.rotM₁φ S)) i
  M.toEuclideanLin.toContinuousLinearMap

-- Helper simp lemmas for rotR and rotR' applied to vectors
@[simp]
private lemma rotR_eq_toEuclideanLin (α : ℝ) :
    (rotR α : ℝ² →L[ℝ] ℝ²) = (rotR_mat α).toEuclideanLin.toContinuousLinearMap := rfl

@[simp]
private lemma rotR'_eq_toEuclideanLin (α : ℝ) :
    rotR' α = (rotR'_mat α).toEuclideanLin.toContinuousLinearMap := rfl

-- Explicit component lemmas for rotR applied to a vector
private lemma rotR_apply_0 (α : ℝ) (v : ℝ²) :
    (rotR α v) 0 = Real.cos α * v 0 - Real.sin α * v 1 := by
  simp [rotR, rotR_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotR_apply_1 (α : ℝ) (v : ℝ²) :
    (rotR α v) 1 = Real.sin α * v 0 + Real.cos α * v 1 := by
  simp [rotR, rotR_mat, Matrix.vecHead, Matrix.vecTail]

private lemma rotR'_apply_0 (α : ℝ) (v : ℝ²) :
    (rotR' α v) 0 = -Real.sin α * v 0 - Real.cos α * v 1 := by
  simp [rotR', rotR'_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotR'_apply_1 (α : ℝ) (v : ℝ²) :
    (rotR' α v) 1 = Real.cos α * v 0 - Real.sin α * v 1 := by
  simp [rotR', rotR'_mat, Matrix.vecHead, Matrix.vecTail]; ring

-- Explicit component lemmas for rotM applied to a vector
private lemma rotM_apply_0 (θ φ : ℝ) (S : ℝ³) :
    (rotM θ φ S) 0 = -Real.sin θ * S 0 + Real.cos θ * S 1 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]

private lemma rotM_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotM θ φ S) 1 = -Real.cos θ * Real.cos φ * S 0 - Real.sin θ * Real.cos φ * S 1 + Real.sin φ * S 2 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_apply_0 (θ φ : ℝ) (S : ℝ³) :
    (rotMθ θ φ S) 0 = -Real.cos θ * S 0 - Real.sin θ * S 1 := by
  simp [rotMθ, rotMθ_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotMθ θ φ S) 1 = Real.sin θ * Real.cos φ * S 0 - Real.cos θ * Real.cos φ * S 1 := by
  simp [rotMθ, rotMθ_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMφ_apply_0 (θ φ : ℝ) (S : ℝ³) :
    (rotMφ θ φ S) 0 = 0 := by
  simp [rotMφ, rotMφ_mat, Matrix.vecHead, Matrix.vecTail]

private lemma rotMφ_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotMφ θ φ S) 1 = Real.cos θ * Real.sin φ * S 0 + Real.sin θ * Real.sin φ * S 1 + Real.cos φ * S 2 := by
  simp [rotMφ, rotMφ_mat, Matrix.vecHead, Matrix.vecTail]; ring

-- Explicit computation of rotprojRM' applied to a vector (component 0)
private lemma rotprojRM'_apply_0 (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 0 =
      d 0 * (pbar.rotR' (pbar.rotM₁ S)) 0 +
      d 1 * (pbar.rotR (pbar.rotM₁θ S)) 0 +
      d 2 * (pbar.rotR (pbar.rotM₁φ S)) 0 := by
  simp only [rotprojRM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply]
  ring

-- Explicit computation of rotprojRM' applied to a vector (component 1)
private lemma rotprojRM'_apply_1 (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 1 =
      d 0 * (pbar.rotR' (pbar.rotM₁ S)) 1 +
      d 1 * (pbar.rotR (pbar.rotM₁θ S)) 1 +
      d 2 * (pbar.rotR (pbar.rotM₁φ S)) 1 := by
  simp only [rotprojRM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply]
  ring

-- Full expansion of rotprojRM'_apply_0 to arithmetic
private lemma rotprojRM'_apply_0_expanded (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 0 =
      d 0 * (-Real.sin pbar.α * (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) -
             Real.cos pbar.α * (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
                                 Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 + Real.sin pbar.φ₁ * S 2)) +
      d 1 * (Real.cos pbar.α * (-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) -
             Real.sin pbar.α * (Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1)) +
      d 2 * (Real.cos pbar.α * 0 -
             Real.sin pbar.α * (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
                                Real.cos pbar.φ₁ * S 2)) := by
  rw [rotprojRM'_apply_0]
  simp only [Pose.rotR', Pose.rotR, Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ]
  rw [rotR'_apply_0, rotR_apply_0, rotR_apply_0, rotM_apply_0, rotM_apply_1,
      rotMθ_apply_0, rotMθ_apply_1, rotMφ_apply_0, rotMφ_apply_1]

-- Full expansion of rotprojRM'_apply_1 to arithmetic
private lemma rotprojRM'_apply_1_expanded (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 1 =
      d 0 * (Real.cos pbar.α * (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) -
             Real.sin pbar.α * (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
                                 Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 + Real.sin pbar.φ₁ * S 2)) +
      d 1 * (Real.sin pbar.α * (-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) +
             Real.cos pbar.α * (Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1)) +
      d 2 * (Real.sin pbar.α * 0 +
             Real.cos pbar.α * (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
                                Real.cos pbar.φ₁ * S 2)) := by
  rw [rotprojRM'_apply_1]
  simp only [Pose.rotR', Pose.rotR, Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ]
  rw [rotR'_apply_1, rotR_apply_1, rotR_apply_1, rotM_apply_0, rotM_apply_1,
      rotMθ_apply_0, rotMθ_apply_1, rotMφ_apply_0, rotMφ_apply_1]

-- Helper lemma: component 0 of rotprojRM in terms of sin/cos
private lemma rotprojRM_component0 (θ φ α : ℝ) (S : ℝ³) :
    (rotprojRM θ φ α S) 0 =
      Real.cos α * (-Real.sin θ * S 0 + Real.cos θ * S 1) -
      Real.sin α * (-Real.cos θ * Real.cos φ * S 0 - Real.sin θ * Real.cos φ * S 1 + Real.sin φ * S 2) := by
  simp [rotprojRM, rotR, rotM, rotR_mat, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  ring

-- Helper lemma: component 1 of rotprojRM in terms of sin/cos
private lemma rotprojRM_component1 (θ φ α : ℝ) (S : ℝ³) :
    (rotprojRM θ φ α S) 1 =
      Real.sin α * (-Real.sin θ * S 0 + Real.cos θ * S 1) +
      Real.cos α * (-Real.cos θ * Real.cos φ * S 0 - Real.sin θ * Real.cos φ * S 1 + Real.sin φ * S 2) := by
  simp [rotprojRM, rotR, rotM, rotR_mat, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  ring

-- Note: Linter reports false positives about seq focus; the <;> is actually needed for ext
set_option linter.unnecessarySeqFocus false in
lemma HasFDerivAt.rotproj_inner (pbar : Pose) (S : ℝ³) (w : ℝ²) :
    (HasFDerivAt (rotproj_inner S w) (rotproj_inner' pbar S w) pbar.innerParams) := by

  have z1 : HasFDerivAt (fun x => (rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S) (rotprojRM' pbar S) pbar.innerParams := by
    -- The function is f(α, θ, φ) = rotR α (rotM θ φ S)
    -- Prove via component-wise HasStrictFDerivAt
    apply HasStrictFDerivAt.hasFDerivAt
    rw [hasStrictFDerivAt_piLp]
    intro i
    -- Define projections for coordinates
    let proj0 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
    let proj1 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)
    let proj2 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ³ => x.ofLp 0) proj0 pbar.innerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.innerParams 0
    have hproj1 : HasStrictFDerivAt (fun x : ℝ³ => x.ofLp 1) proj1 pbar.innerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.innerParams 1
    have hproj2 : HasStrictFDerivAt (fun x : ℝ³ => x.ofLp 2) proj2 pbar.innerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.innerParams 2
    have hsinα := (Real.hasStrictDerivAt_sin pbar.α).comp_hasStrictFDerivAt_of_eq pbar.innerParams
      hproj0 (by simp [Pose.innerParams])
    have hcosα := (Real.hasStrictDerivAt_cos pbar.α).comp_hasStrictFDerivAt_of_eq pbar.innerParams
      hproj0 (by simp [Pose.innerParams])
    have hsinθ := (Real.hasStrictDerivAt_sin pbar.θ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams
      hproj1 (by simp [Pose.innerParams])
    have hcosθ := (Real.hasStrictDerivAt_cos pbar.θ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams
      hproj1 (by simp [Pose.innerParams])
    have hsinφ := (Real.hasStrictDerivAt_sin pbar.φ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams
      hproj2 (by simp [Pose.innerParams])
    have hcosφ := (Real.hasStrictDerivAt_cos pbar.φ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams
      hproj2 (by simp [Pose.innerParams])
    -- Helper lemmas for product terms
    have hA : HasStrictFDerivAt (fun x : ℝ³ => -Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1)
        ((-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) • proj1) pbar.innerParams := by
      have h1 := hsinθ.neg.mul_const (S 0)
      have h2 := hcosθ.mul_const (S 1)
      convert h1.add h2 using 1 <;> ext d <;>
        simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
    have hcosθcosφ : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2))
        (Real.cos pbar.θ₁ • (-(Real.sin pbar.φ₁) • proj2) + Real.cos pbar.φ₁ • (-(Real.sin pbar.θ₁) • proj1))
        pbar.innerParams := hcosθ.mul hcosφ
    have hsinθcosφ : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2))
        (Real.sin pbar.θ₁ • (-(Real.sin pbar.φ₁) • proj2) + Real.cos pbar.φ₁ • (Real.cos pbar.θ₁ • proj1))
        pbar.innerParams := hsinθ.mul hcosφ
    have hB : HasStrictFDerivAt (fun x : ℝ³ => -Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
          Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2)
        ((Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1) • proj1 +
         (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
          Real.cos pbar.φ₁ * S 2) • proj2) pbar.innerParams := by
      have h1 := hcosθcosφ.neg.mul_const (S 0)
      have h2 := hsinθcosφ.mul_const (S 1)
      have h3 := hsinφ.mul_const (S 2)
      convert (h1.sub h2).add h3 using 1 <;> ext d <;>
        simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
              ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul] <;> ring
    fin_cases i
    · -- Component 0: cos(α) * A - sin(α) * B
      simp only [Fin.isValue, show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl]
      have hfunc : (fun x : ℝ³ => ((rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S).ofLp (0 : Fin 2)) =
          fun x => Real.cos (x.ofLp 0) * (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1) -
                   Real.sin (x.ofLp 0) * (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
                     Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2) := by
        ext x
        have := rotprojRM_component0 (x.ofLp 1) (x.ofLp 2) (x.ofLp 0) S
        simp only [rotprojRM, ContinuousLinearMap.coe_comp', Function.comp_apply] at this ⊢
        exact this
      rw [hfunc]
      have hcosA : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 0) *
            (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1))
          (Real.cos pbar.α • ((-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) • proj1) +
           (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) • (-(Real.sin pbar.α) • proj0))
          pbar.innerParams := hcosα.mul hA
      have hsinB : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 0) *
            (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
             Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2))
          (Real.sin pbar.α • ((Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
               Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1) • proj1 +
             (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
              Real.cos pbar.φ₁ * S 2) • proj2) +
           (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 +
            Real.sin pbar.φ₁ * S 2) • (Real.cos pbar.α • proj0))
          pbar.innerParams := hsinα.mul hB
      have hfinal := hcosA.sub hsinB
      refine HasStrictFDerivAt.congr_fderiv hfinal ?_
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show ((rotprojRM' pbar S) d).ofLp 0 = ((rotprojRM' pbar S) d) 0 from rfl]
      rw [rotprojRM'_apply_0_expanded]
      simp only [show proj0 d = d.ofLp 0 from rfl, show proj1 d = d.ofLp 1 from rfl,
                 show proj2 d = d.ofLp 2 from rfl, mul_zero, zero_sub]
      ring
    · -- Component 1: sin(α) * A + cos(α) * B
      simp only [Fin.isValue, show (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) from rfl]
      have hfunc : (fun x : ℝ³ => ((rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S).ofLp (1 : Fin 2)) =
          fun x => Real.sin (x.ofLp 0) * (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1) +
                   Real.cos (x.ofLp 0) * (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
                     Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2) := by
        ext x
        have := rotprojRM_component1 (x.ofLp 1) (x.ofLp 2) (x.ofLp 0) S
        simp only [rotprojRM, ContinuousLinearMap.coe_comp', Function.comp_apply] at this ⊢
        exact this
      rw [hfunc]
      have hsinA : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 0) *
            (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1))
          (Real.sin pbar.α • ((-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) • proj1) +
           (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) • (Real.cos pbar.α • proj0))
          pbar.innerParams := hsinα.mul hA
      have hcosB : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 0) *
            (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
             Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2))
          (Real.cos pbar.α • ((Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
               Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1) • proj1 +
             (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
              Real.cos pbar.φ₁ * S 2) • proj2) +
           (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 +
            Real.sin pbar.φ₁ * S 2) • (-(Real.sin pbar.α) • proj0))
          pbar.innerParams := hcosα.mul hB
      have hfinal := hsinA.add hcosB
      refine HasStrictFDerivAt.congr_fderiv hfinal ?_
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show ((rotprojRM' pbar S) d).ofLp 1 = ((rotprojRM' pbar S) d) 1 from rfl]
      rw [rotprojRM'_apply_1_expanded]
      simp only [show proj0 d = d.ofLp 0 from rfl, show proj1 d = d.ofLp 1 from rfl,
                 show proj2 d = d.ofLp 2 from rfl, mul_zero, zero_add]
      ring

  have step :
    (rotproj_inner' pbar S w) = ((fderivInnerCLM ℝ
            ((rotprojRM (pbar.innerParams.ofLp 1) (pbar.innerParams.ofLp 2) (pbar.innerParams.ofLp 0)) S, w)).comp
        ((rotprojRM' pbar S).prod 0)) := by
    ext d
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
               ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add, real_inner_comm]
    simp only [rotproj_inner', rotprojRM']
    simp only [LinearMap.coe_toContinuousLinearMap']
    simp only [Module.Basis.constr_apply_fintype]
    simp only [Matrix.toEuclideanLin_apply]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_lhs => rw [show (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.equivFun = (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) by
      rw [EuclideanSpace.basisFun_toBasis]; exact @PiLp.basisFun_equivFun 2 ℝ (Fin 3) _ _]
    simp only [WithLp.linearEquiv_apply]
    simp only [WithLp.addEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
    simp only [Fin.isValue, Matrix.cons_val]
    conv_rhs => simp only [Matrix.mulVec, Matrix.of_apply]
    simp only [PiLp.inner_apply, Matrix.mulVec, Matrix.of_apply,
               Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    unfold dotProduct
    simp only [Fin.sum_univ_three, smul_eq_mul]
    ring

  rw [step]
  exact HasFDerivAt.inner ℝ z1 (hasFDerivAt_const w pbar.innerParams)

end GlobalTheorem
