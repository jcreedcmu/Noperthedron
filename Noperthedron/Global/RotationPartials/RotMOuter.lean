/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.Definitions
import Noperthedron.Global.SecondPartialHelpers

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

private lemma outerParams_0 (pbar : Pose ℝ) : pbar.outerParams.ofLp 0 = pbar.θ₂ := by simp [Pose.outerParams]
private lemma outerParams_1 (pbar : Pose ℝ) : pbar.outerParams.ofLp 1 = pbar.φ₂ := by simp [Pose.outerParams]

/-- Coordinate extraction in `E 2`: direction `e_i`, same coordinate (moves). -/
private lemma coord2_same (i : Fin 2) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp i = y.ofLp i + t := by simp

/-- Coordinate extraction in `E 2`: direction `e_i`, different coordinate (fixed). -/
private lemma coord2_other {i j : Fin 2} (hij : j ≠ i) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp j = y.ofLp j := by simp [hij]

/-- The fderiv of rotM applied to a fixed vector P, as a function of (θ, φ). -/
noncomputable
def rotM' (pbar : Pose ℝ) (P : ℝ³) : ℝ² →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMφ pbar.θ₂ pbar.φ₂ P) i
  M.toEuclideanLin.toContinuousLinearMap

lemma rotM'_apply (pbar : Pose ℝ) (P : ℝ³) (d : ℝ²) (i : Fin 2) :
    (rotM' pbar P d) i = d 0 * (rotMθ pbar.θ₂ pbar.φ₂ P) i + d 1 * (rotMφ pbar.θ₂ pbar.φ₂ P) i := by
  simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
  simp only [mul_comm (d.ofLp _)]

lemma Differentiable.rotM_outer (P : ℝ³) :
    Differentiable ℝ fun (x : ℝ²) => (rotM (x 0) (x 1)) P := by
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

@[simp]
lemma rotM'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotM' pbar P (EuclideanSpace.single 0 1) = rotMθ pbar.θ₂ pbar.φ₂ P := by
  ext i; fin_cases i <;> simp [rotM', Matrix.mulVec, Matrix.of_apply]

@[simp]
lemma rotM'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotM' pbar P (EuclideanSpace.single 1 1) = rotMφ pbar.θ₂ pbar.φ₂ P := by
  ext i; fin_cases i <;> simp [rotM', Matrix.mulVec, Matrix.of_apply]

lemma HasFDerivAt.rotM_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ² => rotM (x.ofLp 0) (x.ofLp 1) P) pbar.outerParams :=
    Differentiable.rotM_outer P pbar.outerParams
  -- The derivative is a linear map determined by its values on the standard basis,
  -- which are the one-variable derivatives in θ and φ from `RotationDerivs`.
  have hfd : fderiv ℝ (fun x : ℝ² => rotM (x.ofLp 0) (x.ofLp 1) P) pbar.outerParams =
      rotM' pbar P := by
    refine ContinuousLinearMap.coe_injective
      ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext fun i => ?_)
    fin_cases i <;> simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe, Fin.zero_eta, Fin.mk_one]
    · rw [rotM'_single_0]
      refine fderiv_single_eq hdiff ?_
      simp only [coord2_same, coord2_other (by decide : (1 : Fin 2) ≠ 0),
        outerParams_0, outerParams_1]
      exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotM_θ pbar.θ₂ pbar.φ₂ P)
    · rw [rotM'_single_1]
      refine fderiv_single_eq hdiff ?_
      simp only [coord2_same, coord2_other (by decide : (0 : Fin 2) ≠ 1),
        outerParams_0, outerParams_1]
      exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotM_φ pbar.θ₂ pbar.φ₂ P)
  exact hfd ▸ hdiff.hasFDerivAt

-- Fréchet derivative of rotMθ: columns are [rotMθθ, rotMθφ]
noncomputable def rotMθ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθθ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMθφ pbar.θ₂ pbar.φ₂ P) i
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

lemma rotMθ'_apply (pbar : Pose ℝ) (P : ℝ³) (d : ℝ²) (i : Fin 2) :
    (rotMθ' pbar P d) i = d 0 * (rotMθθ pbar.θ₂ pbar.φ₂ P) i + d 1 * (rotMθφ pbar.θ₂ pbar.φ₂ P) i := by
  simp only [rotMθ', LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
  simp only [mul_comm (d.ofLp _)]

@[simp]
lemma rotMθ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθ' pbar P (EuclideanSpace.single 0 1) = rotMθθ pbar.θ₂ pbar.φ₂ P := by
  ext i; fin_cases i <;> simp [rotMθ', Matrix.mulVec, Matrix.of_apply]

@[simp]
lemma rotMθ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθ' pbar P (EuclideanSpace.single 1 1) = rotMθφ pbar.θ₂ pbar.φ₂ P := by
  ext i; fin_cases i <;> simp [rotMθ', Matrix.mulVec, Matrix.of_apply]

lemma HasFDerivAt.rotMθ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMθ (x.ofLp 0) (x.ofLp 1)) P) (rotMθ' pbar P) pbar.outerParams := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ² => rotMθ (x.ofLp 0) (x.ofLp 1) P)
      pbar.outerParams := differentiableAt_rotMθ_outer P pbar.outerParams
  have hfd : fderiv ℝ (fun x : ℝ² => rotMθ (x.ofLp 0) (x.ofLp 1) P) pbar.outerParams =
      rotMθ' pbar P := by
    refine ContinuousLinearMap.coe_injective
      ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext fun i => ?_)
    fin_cases i <;> simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe, Fin.zero_eta, Fin.mk_one]
    · rw [rotMθ'_single_0]
      refine fderiv_single_eq hdiff ?_
      simp only [coord2_same, coord2_other (by decide : (1 : Fin 2) ≠ 0),
        outerParams_0, outerParams_1]
      exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMθ_θ pbar.θ₂ pbar.φ₂ P)
    · rw [rotMθ'_single_1]
      refine fderiv_single_eq hdiff ?_
      simp only [coord2_same, coord2_other (by decide : (0 : Fin 2) ≠ 1),
        outerParams_0, outerParams_1]
      exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMθ_φ pbar.θ₂ pbar.φ₂ P)
  exact hfd ▸ hdiff.hasFDerivAt

-- Fréchet derivative of rotMφ as a function of (θ, φ)
-- Columns: [rotMθφ, rotMφφ] (derivatives w.r.t. θ, φ respectively)
noncomputable def rotMφ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθφ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMφφ pbar.θ₂ pbar.φ₂ P) i
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

lemma rotMφ'_apply (pbar : Pose ℝ) (P : ℝ³) (d : ℝ²) (i : Fin 2) :
    (rotMφ' pbar P d) i = d 0 * (rotMθφ pbar.θ₂ pbar.φ₂ P) i + d 1 * (rotMφφ pbar.θ₂ pbar.φ₂ P) i := by
  simp only [rotMφ', LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
  simp only [mul_comm (d.ofLp _)]

@[simp]
lemma rotMφ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφ' pbar P (EuclideanSpace.single 0 1) = rotMθφ pbar.θ₂ pbar.φ₂ P := by
  ext i; fin_cases i <;> simp [rotMφ', Matrix.mulVec, Matrix.of_apply]

@[simp]
lemma rotMφ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφ' pbar P (EuclideanSpace.single 1 1) = rotMφφ pbar.θ₂ pbar.φ₂ P := by
  ext i; fin_cases i <;> simp [rotMφ', Matrix.mulVec, Matrix.of_apply]

lemma HasFDerivAt.rotMφ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMφ (x.ofLp 0) (x.ofLp 1)) P) (rotMφ' pbar P) pbar.outerParams := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ² => rotMφ (x.ofLp 0) (x.ofLp 1) P)
      pbar.outerParams := differentiableAt_rotMφ_outer P pbar.outerParams
  have hfd : fderiv ℝ (fun x : ℝ² => rotMφ (x.ofLp 0) (x.ofLp 1) P) pbar.outerParams =
      rotMφ' pbar P := by
    refine ContinuousLinearMap.coe_injective
      ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext fun i => ?_)
    fin_cases i <;> simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe, Fin.zero_eta, Fin.mk_one]
    · rw [rotMφ'_single_0]
      refine fderiv_single_eq hdiff ?_
      simp only [coord2_same, coord2_other (by decide : (1 : Fin 2) ≠ 0),
        outerParams_0, outerParams_1]
      exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMφ_θ pbar.θ₂ pbar.φ₂ P)
    · rw [rotMφ'_single_1]
      refine fderiv_single_eq hdiff ?_
      simp only [coord2_same, coord2_other (by decide : (0 : Fin 2) ≠ 1),
        outerParams_0, outerParams_1]
      exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMφ_φ pbar.θ₂ pbar.φ₂ P)
  exact hfd ▸ hdiff.hasFDerivAt

end GlobalTheorem
