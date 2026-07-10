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

/-- The fderiv of rotM applied to a fixed vector P, as a function of (θ, φ).
Columns: [rotMθ, rotMφ]. -/
noncomputable
def rotM' (pbar : Pose ℝ) (P : ℝ³) : ℝ² →L[ℝ] ℝ² :=
  columnsCLM ![rotMθ pbar.θ₂ pbar.φ₂ P, rotMφ pbar.θ₂ pbar.φ₂ P]

lemma Differentiable.rotM_outer (P : ℝ³) :
    Differentiable ℝ fun (x : ℝ²) => (rotM (x 0) (x 1)) P :=
  differentiable_rotM_comp (by fun_prop) (by fun_prop) (differentiable_const P)

@[simp]
lemma rotM'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotM' pbar P (EuclideanSpace.single 0 1) = rotMθ pbar.θ₂ pbar.φ₂ P := by
  simp [rotM']

@[simp]
lemma rotM'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotM' pbar P (EuclideanSpace.single 1 1) = rotMφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotM']

lemma HasFDerivAt.rotM_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams := by
  simpa [rotM', Pose.outerParams] using
    hasFDerivAt_two_params (fun θ φ => rotM θ φ P) pbar.outerParams
      (rotMθ pbar.θ₂ pbar.φ₂ P) (rotMφ pbar.θ₂ pbar.φ₂ P)
      (Differentiable.rotM_outer P pbar.outerParams)
      (by simpa [Pose.outerParams] using hasDerivAt_rotM_θ pbar.θ₂ pbar.φ₂ P)
      (by simpa [Pose.outerParams] using hasDerivAt_rotM_φ pbar.θ₂ pbar.φ₂ P)

/-- Fréchet derivative of rotMθ: columns are [rotMθθ, rotMθφ]. -/
noncomputable def rotMθ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  columnsCLM ![rotMθθ pbar.θ₂ pbar.φ₂ P, rotMθφ pbar.θ₂ pbar.φ₂ P]

@[simp]
lemma rotMθ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθ' pbar P (EuclideanSpace.single 0 1) = rotMθθ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMθ']

@[simp]
lemma rotMθ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθ' pbar P (EuclideanSpace.single 1 1) = rotMθφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMθ']

lemma HasFDerivAt.rotMθ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMθ (x.ofLp 0) (x.ofLp 1)) P) (rotMθ' pbar P) pbar.outerParams := by
  simpa [rotMθ', Pose.outerParams] using
    hasFDerivAt_two_params (fun θ φ => rotMθ θ φ P) pbar.outerParams
      (rotMθθ pbar.θ₂ pbar.φ₂ P) (rotMθφ pbar.θ₂ pbar.φ₂ P)
      (differentiableAt_rotMθ_outer P pbar.outerParams)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMθ_θ pbar.θ₂ pbar.φ₂ P)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMθ_φ pbar.θ₂ pbar.φ₂ P)

/-- Fréchet derivative of rotMφ: columns are [rotMθφ, rotMφφ]. -/
noncomputable def rotMφ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  columnsCLM ![rotMθφ pbar.θ₂ pbar.φ₂ P, rotMφφ pbar.θ₂ pbar.φ₂ P]

@[simp]
lemma rotMφ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφ' pbar P (EuclideanSpace.single 0 1) = rotMθφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMφ']

@[simp]
lemma rotMφ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφ' pbar P (EuclideanSpace.single 1 1) = rotMφφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMφ']

lemma HasFDerivAt.rotMφ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMφ (x.ofLp 0) (x.ofLp 1)) P) (rotMφ' pbar P) pbar.outerParams := by
  simpa [rotMφ', Pose.outerParams] using
    hasFDerivAt_two_params (fun θ φ => rotMφ θ φ P) pbar.outerParams
      (rotMθφ pbar.θ₂ pbar.φ₂ P) (rotMφφ pbar.θ₂ pbar.φ₂ P)
      (differentiableAt_rotMφ_outer P pbar.outerParams)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMφ_θ pbar.θ₂ pbar.φ₂ P)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMφ_φ pbar.θ₂ pbar.φ₂ P)

/-- Fréchet derivative of rotMθθ: columns are [-rotMθ, rotMθθφ] (Mθθθ = -Mθ). -/
noncomputable def rotMθθ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  columnsCLM ![-(rotMθ pbar.θ₂ pbar.φ₂ P), rotMθθφ pbar.θ₂ pbar.φ₂ P]

@[simp]
lemma rotMθθ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθθ' pbar P (EuclideanSpace.single 0 1) = -(rotMθ pbar.θ₂ pbar.φ₂ P) := by
  simp [rotMθθ']

@[simp]
lemma rotMθθ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθθ' pbar P (EuclideanSpace.single 1 1) = rotMθθφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMθθ']

lemma HasFDerivAt.rotMθθ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMθθ (x.ofLp 0) (x.ofLp 1)) P) (rotMθθ' pbar P) pbar.outerParams := by
  simpa [rotMθθ', Pose.outerParams] using
    hasFDerivAt_two_params (fun θ φ => rotMθθ θ φ P) pbar.outerParams
      (-(rotMθ pbar.θ₂ pbar.φ₂ P)) (rotMθθφ pbar.θ₂ pbar.φ₂ P)
      (differentiableAt_rotMθθ_outer P pbar.outerParams)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMθθ_θ pbar.θ₂ pbar.φ₂ P)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMθθ_φ pbar.θ₂ pbar.φ₂ P)

/-- Fréchet derivative of rotMθφ: columns are [rotMθθφ, rotMθφφ]. -/
noncomputable def rotMθφ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  columnsCLM ![rotMθθφ pbar.θ₂ pbar.φ₂ P, rotMθφφ pbar.θ₂ pbar.φ₂ P]

@[simp]
lemma rotMθφ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθφ' pbar P (EuclideanSpace.single 0 1) = rotMθθφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMθφ']

@[simp]
lemma rotMθφ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθφ' pbar P (EuclideanSpace.single 1 1) = rotMθφφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMθφ']

lemma HasFDerivAt.rotMθφ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMθφ (x.ofLp 0) (x.ofLp 1)) P) (rotMθφ' pbar P) pbar.outerParams := by
  simpa [rotMθφ', Pose.outerParams] using
    hasFDerivAt_two_params (fun θ φ => rotMθφ θ φ P) pbar.outerParams
      (rotMθθφ pbar.θ₂ pbar.φ₂ P) (rotMθφφ pbar.θ₂ pbar.φ₂ P)
      (differentiableAt_rotMθφ_outer P pbar.outerParams)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMθφ_θ pbar.θ₂ pbar.φ₂ P)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMθφ_φ pbar.θ₂ pbar.φ₂ P)

/-- Fréchet derivative of rotMφφ: columns are [rotMθφφ, -rotMφ] (Mφφφ = -Mφ). -/
noncomputable def rotMφφ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  columnsCLM ![rotMθφφ pbar.θ₂ pbar.φ₂ P, -(rotMφ pbar.θ₂ pbar.φ₂ P)]

@[simp]
lemma rotMφφ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφφ' pbar P (EuclideanSpace.single 0 1) = rotMθφφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMφφ']

@[simp]
lemma rotMφφ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφφ' pbar P (EuclideanSpace.single 1 1) = -(rotMφ pbar.θ₂ pbar.φ₂ P) := by
  simp [rotMφφ']

lemma HasFDerivAt.rotMφφ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMφφ (x.ofLp 0) (x.ofLp 1)) P) (rotMφφ' pbar P) pbar.outerParams := by
  simpa [rotMφφ', Pose.outerParams] using
    hasFDerivAt_two_params (fun θ φ => rotMφφ θ φ P) pbar.outerParams
      (rotMθφφ pbar.θ₂ pbar.φ₂ P) (-(rotMφ pbar.θ₂ pbar.φ₂ P))
      (differentiableAt_rotMφφ_outer P pbar.outerParams)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMφφ_θ pbar.θ₂ pbar.φ₂ P)
      (by simpa [Pose.outerParams] using hasDerivAt_rotMφφ_φ pbar.θ₂ pbar.φ₂ P)

end GlobalTheorem
