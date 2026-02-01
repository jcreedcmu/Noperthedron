/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationPartials.SecondPartialOuter

/-!
# Second Partial Inner Lemmas

This file contains:
- **`second_partial_inner_rotM_inner`** (9 cases)
- **`rotation_partials_bounded`** (the main theorem from [SY25] Lemma 19)
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## Helper lemmas for composition norm bounds
-/

private lemma comp_norm_le_one' {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖A ∘L B‖ ≤ 1 := by
  calc ‖A ∘L B‖ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le A B
    _ ≤ 1 * 1 := by apply mul_le_mul hA hB (norm_nonneg _) (by linarith)
    _ = 1 := by ring

private lemma neg_comp_norm_le_one' {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖-(A ∘L B)‖ ≤ 1 := by
  rw [norm_neg]
  exact comp_norm_le_one' hA hB

/-- Bound for |⟪A S, w⟫ / ‖S‖| when ‖A‖ ≤ 1 and ‖w‖ = 1. -/
private lemma inner_bound_helper' (A : ℝ³ →L[ℝ] ℝ²) (S : ℝ³) (w : ℝ²)
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

set_option maxHeartbeats 400000 in
private lemma second_partial_rotM_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j : Fin 3) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (rotproj_inner S w)) x = ⟪A S, w⟫ := by
  let α := x.ofLp 0; let θ := x.ofLp 1; let φ := x.ofLp 2
  fin_cases i <;> fin_cases j
  · -- (0, 0): ∂²/∂α² → -(rotR α ∘L rotM θ φ)
    refine ⟨-(rotR α ∘L rotM θ φ), ?_, ?_⟩
    · exact neg_comp_norm_le_one' (le_of_eq (Bounding.rotR_norm_one α)) (le_of_eq (Bounding.rotM_norm_one θ φ))
    · show nth_partial 0 (nth_partial 0 (rotproj_inner S w)) x = ⟪(-(rotR α ∘L rotM θ φ)) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) =
          ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e0 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1)) =
          fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 0 1) (differentiableAt_rotR'_rotM S x)]
      have hfderiv_rotR' : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 0 1) = -(rotR α (rotM θ φ S)) :=
        fderiv_rotR'_rotM_in_e0 S x α θ φ rfl rfl rfl (differentiableAt_rotR'_rotM S x)
      rw [hfderiv_rotR']
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply, inner_neg_left]
  · -- (0, 1): ∂²/∂α∂θ → rotR' α ∘L rotMθ θ φ
    refine ⟨rotR' α ∘L rotMθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMθ_norm_le_one θ φ)
    · show nth_partial 0 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMθ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) =
          ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y
        set pbar : Pose := ⟨y.ofLp 1, 0, y.ofLp 2, 0, y.ofLp 0⟩ with hpbar_def
        have hpbar : pbar.innerParams = y := by ext i; fin_cases i <;> rfl
        rw [← hpbar, (HasFDerivAt.rotproj_inner pbar S w).fderiv, hpbar]
        simp only [rotproj_inner', hpbar_def, Pose.rotR, Pose.rotM₁θ,
          LinearMap.coe_toContinuousLinearMap']
        have hbasis : EuclideanSpace.single 1 1 = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis 1 := by
          ext i; simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]
        rw [hbasis, Module.Basis.constr_basis]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 0 1) (differentiableAt_rotR_rotMθ S x)]
      have hfderiv_rotR : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 0 1) = rotR' α (rotMθ θ φ S) := by
        let proj0 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
        have hproj0 : HasFDerivAt (fun z : ℝ³ => z.ofLp 0) proj0 x :=
          (PiLp.hasStrictFDerivAt_apply 2 x 0).hasFDerivAt
        have hderiv : HasDerivAt (fun α' => rotR α' (rotMθ θ φ S)) (rotR' α (rotMθ θ φ S)) α :=
          HasDerivAt_rotR α (rotMθ θ φ S)
        have hfderiv : HasFDerivAt (fun α' : ℝ => rotR α' (rotMθ θ φ S))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMθ θ φ S))) α := hderiv.hasFDerivAt
        have hcomp' : HasFDerivAt ((fun α' => rotR α' (rotMθ θ φ S)) ∘ (fun z : E 3 => z.ofLp 0))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMθ θ φ S)) ∘L proj0) x :=
          hfderiv.comp x hproj0
        have heq_form : ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMθ θ φ S)) ∘L proj0 =
            proj0.smulRight (rotR' α (rotMθ θ φ S)) := by
          ext y; simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
        have hcomp : HasFDerivAt ((fun α' => rotR α' (rotMθ θ φ S)) ∘ (fun z : E 3 => z.ofLp 0))
            (proj0.smulRight (rotR' α (rotMθ θ φ S))) x := by rw [← heq_form]; exact hcomp'
        have hdiff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMθ S x
        have heq_fderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 0 1) =
            (fderiv ℝ ((fun α' => rotR α' (rotMθ θ φ S)) ∘ (fun z : E 3 => z.ofLp 0)) x) (EuclideanSpace.single 0 1) := by
          have hLHS : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 0 1) =
              rotR' α (rotMθ θ φ S) := by
            rw [← hdiff.lineDeriv_eq_fderiv]
            have hline : HasLineDerivAt ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S))
                (rotR' α (rotMθ θ φ S)) x (EuclideanSpace.single 0 1) := by
              unfold HasLineDerivAt
              have hsimp : ∀ t, rotR ((x + t • EuclideanSpace.single 0 1).ofLp 0) (rotMθ ((x + t • EuclideanSpace.single 0 1).ofLp 1) ((x + t • EuclideanSpace.single 0 1).ofLp 2) S) =
                  rotR (α + t) (rotMθ θ φ S) := by
                intro t
                have h0 : (x + t • EuclideanSpace.single 0 1).ofLp 0 = x.ofLp 0 + t := coord_e0_same x t
                rw [h0, coord_e0_at1, coord_e0_at2]
              simp_rw [hsimp]
              have hrotR : HasDerivAt (fun a => rotR a (rotMθ θ φ S)) (rotR' α (rotMθ θ φ S)) α := HasDerivAt_rotR _ _
              have hid : HasDerivAt (fun t : ℝ => α + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add α
              have hrotR' : HasDerivAt (fun a => rotR a (rotMθ θ φ S)) (rotR' (α + 0) (rotMθ θ φ S)) (α + 0) := by simp only [add_zero]; exact hrotR
              have hcomp' := hrotR'.scomp 0 hid
              simp only [one_smul, add_zero] at hcomp'
              have heq_fun : ((fun a ↦ rotR a (rotMθ θ φ S)) ∘ HAdd.hAdd α) = (fun t => rotR (α + t) (rotMθ θ φ S)) := by ext t; simp only [Function.comp_apply]
              rw [heq_fun] at hcomp'; exact hcomp'
            exact hline.lineDeriv
          rw [hLHS, hcomp.fderiv]
          simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply, EuclideanSpace.single_apply, ↓reduceIte, one_smul]
        rw [heq_fderiv, hcomp.fderiv]
        simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
          EuclideanSpace.single_apply, ↓reduceIte, one_smul]
      rw [hfderiv_rotR]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (0, 2): ∂²/∂α∂φ → rotR' α ∘L rotMφ θ φ
    refine ⟨rotR' α ∘L rotMφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMφ_norm_le_one θ φ)
    · show nth_partial 0 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) =
          ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e2 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 0 1) (differentiableAt_rotR_rotMφ S x)]
      have hfderiv_rotR : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 0 1) = rotR' α (rotMφ θ φ S) :=
        fderiv_rotR_any_M_in_e0 S x rotMφ (differentiableAt_rotR_rotMφ S x)
      rw [hfderiv_rotR]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (1, 0): ∂²/∂θ∂α → rotR' α ∘L rotMθ θ φ (same as (0,1))
    refine ⟨rotR' α ∘L rotMθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMθ_norm_le_one θ φ)
    · show nth_partial 1 (nth_partial 0 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMθ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) =
          ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e0 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1)) =
          fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 1 1) (differentiableAt_rotR'_rotM S x)]
      have hfderiv : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 1 1) = rotR' α (rotMθ θ φ S) :=
        fderiv_rotR'_rotM_in_e1 S x α θ φ rfl rfl rfl (differentiableAt_rotR'_rotM S x)
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (1, 1): ∂²/∂θ² → rotR α ∘L rotMθθ θ φ
    refine ⟨rotR α ∘L rotMθθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθθ_norm_le_one θ φ)
    · show nth_partial 1 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθθ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) =
          ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e1 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 1 1) (differentiableAt_rotR_rotMθ S x)]
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 1 1) = rotR α (rotMθθ θ φ S) := fderiv_rotR_rotMθ_in_e1 S x
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (1, 2): ∂²/∂θ∂φ → rotR α ∘L rotMθφ θ φ
    refine ⟨rotR α ∘L rotMθφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθφ_norm_le_one θ φ)
    · show nth_partial 1 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) =
          ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e2 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 1 1) (differentiableAt_rotR_rotMφ S x)]
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 1 1) = rotR α (rotMθφ θ φ S) := fderiv_rotR_rotMφ_in_e1 S x
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (2, 0): ∂²/∂φ∂α → rotR' α ∘L rotMφ θ φ (same as (0,2))
    refine ⟨rotR' α ∘L rotMφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMφ_norm_le_one θ φ)
    · show nth_partial 2 (nth_partial 0 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) =
          ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e0 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1)) =
          fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 2 1) (differentiableAt_rotR'_rotM S x)]
      have hfderiv : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 2 1) = rotR' α (rotMφ θ φ S) := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR'_rotM S x
        rw [← hf_diff.lineDeriv_eq_fderiv]
        have hline : HasLineDerivAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))
            (rotR' α (rotMφ θ φ S)) x (EuclideanSpace.single 2 1) := by
          unfold HasLineDerivAt
          have hsimp : ∀ t, rotR' ((x + t • EuclideanSpace.single 2 1).ofLp 0)
              (rotM ((x + t • EuclideanSpace.single 2 1).ofLp 1) ((x + t • EuclideanSpace.single 2 1).ofLp 2) S) =
              rotR' α (rotM θ (φ + t) S) := by
            intro t
            have h2 : (x + t • EuclideanSpace.single 2 1).ofLp 2 = x.ofLp 2 + t := coord_e2_same x t
            rw [coord_e2_at0, coord_e2_at1, h2]
          simp_rw [hsimp]
          have hrotM : HasDerivAt (fun φ' => rotM θ φ' S) (rotMφ θ φ S) φ := hasDerivAt_rotM_φ θ φ S
          have hR : HasFDerivAt (fun v => rotR' α v) (rotR' α) (rotM θ φ S) := ContinuousLinearMap.hasFDerivAt (rotR' α)
          have hrotM_fderiv : HasFDerivAt (fun φ' : ℝ => rotM θ φ' S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ θ φ S)) φ := hrotM.hasFDerivAt
          have hcomp_inner := hR.comp φ hrotM_fderiv
          have heq_comp : (rotR' α).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ θ φ S)) =
              ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMφ θ φ S)) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
          rw [heq_comp] at hcomp_inner
          have hcomp_deriv : HasDerivAt ((fun v => rotR' α v) ∘ (fun φ' => rotM θ φ' S)) (rotR' α (rotMφ θ φ S)) φ := by
            have h := hcomp_inner.hasDerivAt (x := φ)
            simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h; exact h
          have hid : HasDerivAt (fun t : ℝ => φ + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add φ
          have hcomp_deriv' : HasDerivAt (fun φ' => rotR' α (rotM θ φ' S)) (rotR' α (rotMφ θ (φ + 0) S)) (φ + 0) := by
            simp only [add_zero] at hcomp_deriv ⊢; exact hcomp_deriv
          have hfinal := hcomp_deriv'.scomp 0 hid
          simp only [one_smul, add_zero] at hfinal
          have heq_fun : ((fun φ' => rotR' α (rotM θ φ' S)) ∘ HAdd.hAdd φ) =
              (fun t => rotR' α (rotM θ (φ + t) S)) := by ext t; simp only [Function.comp_apply]
          rw [heq_fun] at hfinal; exact hfinal
        exact hline.lineDeriv
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (2, 1): ∂²/∂φ∂θ → rotR α ∘L rotMθφ θ φ (same as (1,2))
    refine ⟨rotR α ∘L rotMθφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθφ_norm_le_one θ φ)
    · show nth_partial 2 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) =
          ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e1 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 2 1) (differentiableAt_rotR_rotMθ S x)]
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 2 1) = rotR α (rotMθφ θ φ S) := fderiv_rotR_rotMθ_in_e2 S x
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (2, 2): ∂²/∂φ² → rotR α ∘L rotMφφ θ φ
    refine ⟨rotR α ∘L rotMφφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one' (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMφφ_norm_le_one θ φ)
    · show nth_partial 2 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMφφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) =
          ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff := differentiableAt_rotR_rotM S y
        rw [fderiv_inner_const _ w y _ hf_diff, fderiv_rotR_rotM_in_e2 S y hf_diff]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      rw [fderiv_inner_const _ w x (EuclideanSpace.single 2 1) (differentiableAt_rotR_rotMφ S x)]
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 2 1) = rotR α (rotMφφ θ φ S) := fderiv_rotR_rotMφ_in_e2 S x
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]

/-!
## Main theorems
-/

/- [SY25] Lemma 19 (inner part) -/
theorem second_partial_inner_rotM_inner (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) (i j : Fin 3) (y : ℝ³) :
    |(fderiv ℝ (fun z => (fderiv ℝ (rotproj_inner_unit S w) z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single j 1)| ≤ 1 := by
  by_cases hS : ‖S‖ = 0
  · have hzero : rotproj_inner_unit S w = 0 := by ext y; simp [rotproj_inner_unit, hS]
    simp only [hzero, fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply]
    norm_num
  · have S_pos : ‖S‖ > 0 := (norm_nonneg S).lt_of_ne' hS
    have heq : rotproj_inner_unit S w = fun z => rotproj_inner S w z / ‖S‖ := by ext z; rfl
    have hgoal : (fderiv ℝ (fun z => (fderiv ℝ (rotproj_inner_unit S w) z) (EuclideanSpace.single i 1)) y)
        (EuclideanSpace.single j 1) = nth_partial j (nth_partial i (rotproj_inner_unit S w)) y := by
      unfold nth_partial; rfl
    rw [hgoal]
    have hf_smooth : ContDiff ℝ 2 (rotproj_inner S w) := by
      have heq_inner : rotproj_inner S w = ‖S‖ • rotproj_inner_unit S w := by
        ext x; simp [rotproj_inner, rotproj_inner_unit, mul_div_cancel₀ _ (ne_of_gt S_pos)]
      rw [heq_inner]
      have h2 : ContDiff ℝ 2 (rotproj_inner_unit S w) := rotation_partials_exist S_pos
      exact contDiff_const.smul h2
    have hdiv : (fun z => rotproj_inner S w z / ‖S‖) = ‖S‖⁻¹ • (rotproj_inner S w) := by
      ext z; simp [div_eq_inv_mul, smul_eq_mul]
    have hpartial_smul : nth_partial i (‖S‖⁻¹ • rotproj_inner S w) =
        ‖S‖⁻¹ • nth_partial i (rotproj_inner S w) := by
      ext z
      simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
      have h2ne : (2 : WithTop ℕ∞) ≠ 0 := by decide
      rw [fderiv_const_smul (c := ‖S‖⁻¹) (hf_smooth.differentiable h2ne z)]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hg : ContDiff ℝ 1 (nth_partial i (rotproj_inner S w)) := by
      unfold nth_partial
      have h : (1 : WithTop ℕ∞) + 1 ≤ 2 := by decide
      exact hf_smooth.fderiv_right h |>.clm_apply contDiff_const
    have hg_diff : Differentiable ℝ (nth_partial i (rotproj_inner S w)) := by
      have h1ne : (1 : WithTop ℕ∞) ≠ 0 := by decide
      exact hg.differentiable h1ne
    have hpartial_smul2 : nth_partial j (‖S‖⁻¹ • nth_partial i (rotproj_inner S w)) =
        ‖S‖⁻¹ • nth_partial j (nth_partial i (rotproj_inner S w)) := by
      ext z
      simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
      rw [fderiv_const_smul (c := ‖S‖⁻¹) (hg_diff z)]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hscale : nth_partial j (nth_partial i (rotproj_inner_unit S w)) y =
        nth_partial j (nth_partial i (rotproj_inner S w)) y / ‖S‖ := by
      rw [heq, hdiv, hpartial_smul, hpartial_smul2]
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hscale]
    obtain ⟨A, hAnorm, hAeq⟩ := second_partial_rotM_inner_eq S w y j i
    rw [hAeq]
    exact inner_bound_helper' A S w w_unit hAnorm

/- [SY25] Lemma 19 -/
theorem rotation_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_inner_unit S w) := by
  intro x i j
  have hgoal : (nth_partial i <| nth_partial j <| rotproj_inner_unit S w) x =
      (fderiv ℝ (fun z => (fderiv ℝ (rotproj_inner_unit S w) z) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) := by
    unfold nth_partial; rfl
  rw [hgoal]
  exact second_partial_inner_rotM_inner S w_unit j i x

end GlobalTheorem
