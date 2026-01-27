import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Noperthedron.RotationDerivs
import Noperthedron.Nopert
import Noperthedron.PoseInterval
import Noperthedron.Global.Basic
import Noperthedron.Global.BoundedPartialsControlDifference
import Noperthedron.Global.SecondPartialHelpers

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma f_le_max {n : ℕ} {V : Finset (E n)} (Vne : V.Nonempty) (w : E n → ℝ) (hw1 : ∀ y ∈ V, 0 ≤ w y)
      (f : E n →ₗ[ℝ] ℝ) :
  ↑(∑ x ∈ V, w x * f x) ≤ ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max' (by simp [Finset.image_nonempty]; exact Vne) := by
  have fx_le_fvmax (x : V) : f x ≤ (Finset.image f V).max' (by simp [Finset.image_nonempty]; exact Vne) := by
    refine Finset.le_max' _ _ ?_
    simp only [Finset.mem_image]
    exact ⟨x, Finset.coe_mem x, rfl⟩
  push_cast
  refine Finset.sum_le_sum ?_
  intro x hx
  grw [fx_le_fvmax ⟨x, hx⟩]
  exact hw1 x hx

private lemma extract_constant {n : ℕ} {V : Finset (E n)} (w : E n → ℝ)
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max = ↑(∑ x ∈ V, w x) * (Finset.image (⇑f) V).max := by
  let ⟨S', hS'⟩ := convexHull_nonempty_iff.mp ⟨S, hs⟩
  let ⟨m, hm⟩ := Finset.max_of_mem (Finset.mem_image_of_mem f hS')
  rw [hm]
  suffices h : (WithBot.some (∑ x ∈ V, (w x) * m)) = WithBot.some ((∑ x ∈ V, w x) * m) by
    push_cast at h ⊢
    exact h
  refine congrArg WithBot.some ?_
  rw [← Finset.sum_mul]

theorem finset_hull_linear_max {n : ℕ} {V : Finset (E n)} (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ (V.image f).max' (by simp [Finset.image_nonempty]; exact Vne) := by
  have Vine : (V.image f).Nonempty := by simp [Finset.image_nonempty]; exact Vne
  have hs_orig := hs
  rw [Finset.convexHull_eq] at hs
  obtain ⟨w, hw1, hw2, hw3⟩ := hs
  calc
    (f S) = (f (∑ i ∈ V, w i • id i)) := by rw [← hw3, Finset.centerMass_eq_of_sum_1 V id hw2]
    _       = ∑ x ∈ V, w x * f x := by simp
    _       ≤ ∑ x ∈ V, w x * ((Finset.image f V).max' Vine) := f_le_max Vne w hw1 f
    _       = (∑ x ∈ V, w x) * ((Finset.image f V).max' Vine) := by rw [← Finset.sum_mul]
    _       = (Finset.image f V).max' (by simp [Finset.image_nonempty]; exact Vne) := by rw [hw2]; simp

/- [SY25] Lemma 18 -/
theorem hull_scalar_prod {n : ℕ} (V : Finset (E n)) (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (w : E n) :
    ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) (by simp [Finset.image_nonempty]; exact Vne) := by
  exact finset_hull_linear_max Vne S hs (InnerProductSpace.toDual ℝ (E n) w |>.toLinearMap)

noncomputable
def rotproj_inner (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫

noncomputable
def rotproj_inner_unit (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫ / ‖S‖

noncomputable
def rotproj_outer_unit (S : ℝ³) (w : ℝ²) (x : ℝ²) : ℝ :=
  ⟪rotM (x 0) (x 1) S, w⟫ / ‖S‖

noncomputable
def rotproj_outer (S : ℝ³) (w : ℝ²) (x : ℝ²) : ℝ :=
  ⟪rotM (x 0) (x 1) S, w⟫

/--
An explicit formula for the full derivative of rotproj_outer as a function ℝ² → ℝ
-/
noncomputable
def rotproj_outer' (pbar : Pose) (P : ℝ³) (w : ℝ²) : ℝ² →L[ℝ] ℝ :=
  let grad : Fin 2 → ℝ := ![
    ⟪pbar.rotM₂θ P, w⟫,
    ⟪pbar.rotM₂φ P, w⟫
  ]
  EuclideanSpace.basisFun (Fin 2) ℝ |>.toBasis.constr ℝ grad |>.toContinuousLinearMap

lemma rotation_partials_exist {S : ℝ³} (S_nonzero : ‖S‖ > 0) {w : ℝ²} :
    ContDiff ℝ 2 (rotproj_inner_unit S w) := by
  refine ContDiff.div ?_ contDiff_const (fun x ↦ (ne_of_lt S_nonzero).symm)
  simp [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

lemma rotation_partials_exist_outer {S : ℝ³} (S_nonzero : ‖S‖ > 0) {w : ℝ²} :
    ContDiff ℝ 2 (rotproj_outer_unit S w) := by
  refine ContDiff.div ?_ contDiff_const (fun x ↦ (ne_of_lt S_nonzero).symm)
  simp [inner, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

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

-- Derivative of rotR' with respect to α: d/dα(rotR' α v) = -rotR α v
-- This is needed for the second derivative ∂²/∂α² of rotproj_inner
private lemma HasDerivAt_rotR' (α : ℝ) (v : ℝ²) :
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

-- First derivatives of rotM w.r.t. angles
-- These are needed for computing first partial derivatives of rotproj_inner

-- Derivative of rotM w.r.t. θ gives rotMθ
private lemma hasDerivAt_rotM_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotM θ' φ S) (rotMθ θ φ S) θ := by
  have h_f : (fun θ' => rotM θ' φ S) = (fun θ' => !₂[-Real.sin θ' * S 0 + Real.cos θ' * S 1,
      -Real.cos θ' * Real.cos φ * S 0 - Real.sin θ' * Real.cos φ * S 1 + Real.sin φ * S 2]) := by
    ext θ' i; fin_cases i <;> simp [rotM, rotM_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMθ θ φ S = !₂[-Real.cos θ * S 0 - Real.sin θ * S 1,
      Real.sin θ * Real.cos φ * S 0 - Real.cos θ * Real.cos φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · have h : deriv (fun x => -Real.sin x * S 0 + Real.cos x * S 1) θ = -Real.cos θ * S 0 - Real.sin θ * S 1 := by simp; ring
    rw [← h]; exact DifferentiableAt.hasDerivAt (by fun_prop)
  · -- -cos θ * cos φ * S 0 - sin θ * cos φ * S 1 + sin φ * S 2
    have h1 : HasDerivAt (fun x => -Real.cos x * Real.cos φ * S 0) (Real.sin θ * Real.cos φ * S 0) θ := by
      have := (Real.hasDerivAt_cos θ).neg.mul_const (Real.cos φ * S 0)
      simp only [neg_neg, mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin x * Real.cos φ * S 1) (Real.cos θ * Real.cos φ * S 1) θ := by
      have := (Real.hasDerivAt_sin θ).mul_const (Real.cos φ * S 1)
      simp only [mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun _ : ℝ => Real.sin φ * S 2) 0 θ := hasDerivAt_const _ _
    convert (h1.sub h2).add h3 using 1; ring

-- Derivative of rotM w.r.t. φ gives rotMφ
private lemma hasDerivAt_rotM_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotM θ φ' S) (rotMφ θ φ S) φ := by
  have h_f : (fun φ' => rotM θ φ' S) = (fun φ' => !₂[-Real.sin θ * S 0 + Real.cos θ * S 1,
      -Real.cos θ * Real.cos φ' * S 0 - Real.sin θ * Real.cos φ' * S 1 + Real.sin φ' * S 2]) := by
    ext φ' i; fin_cases i <;> simp [rotM, rotM_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMφ θ φ S = !₂[(0 : ℝ),
      Real.cos θ * Real.sin φ * S 0 + Real.sin θ * Real.sin φ * S 1 + Real.cos φ * S 2] := by
    ext i; fin_cases i <;> simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · -- -cos θ * cos φ * S 0 - sin θ * cos φ * S 1 + sin φ * S 2 → cos θ * sin φ * S 0 + sin θ * sin φ * S 1 + cos φ * S 2
    have h1 : HasDerivAt (fun x => -Real.cos θ * Real.cos x * S 0) (Real.cos θ * Real.sin φ * S 0) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (-Real.cos θ)).mul_const (S 0)
      simp only [neg_mul, mul_neg, neg_neg, mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin θ * Real.cos x * S 1) (-Real.sin θ * Real.sin φ * S 1) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (Real.sin θ)).mul_const (S 1)
      simp only [neg_mul, mul_neg, mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun x => Real.sin x * S 2) (Real.cos φ * S 2) φ := (Real.hasDerivAt_sin φ).mul_const (S 2)
    convert (h1.sub h2).add h3 using 1; ring

-- Derivatives of rotation matrix partials w.r.t. angles
-- These are needed for computing second derivatives of rotproj functions
-- Each proves HasDerivAt for the rotation matrix derivative applied to a fixed vector S

-- The proofs follow by expanding the matrix definitions and differentiating component-wise
-- using HasDerivAt.add, HasDerivAt.mul_const, Real.hasDerivAt_sin, Real.hasDerivAt_cos
private lemma hasDerivAt_rotMθ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθ θ' φ S) (rotMθθ θ φ S) θ := by
  have h_f : (fun θ' => rotMθ θ' φ S) = (fun θ' => !₂[-Real.cos θ' * S 0 - Real.sin θ' * S 1,
      Real.sin θ' * Real.cos φ * S 0 - Real.cos θ' * Real.cos φ * S 1]) := by
    ext θ' i; fin_cases i <;> simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMθθ θ φ S = !₂[Real.sin θ * S 0 - Real.cos θ * S 1,
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · have h : deriv (fun x => -Real.cos x * S 0 - Real.sin x * S 1) θ = Real.sin θ * S 0 - Real.cos θ * S 1 := by simp
    rw [← h]; exact DifferentiableAt.hasDerivAt (by fun_prop)
  · have h1 : HasDerivAt (fun x => Real.sin x * Real.cos φ * S 0) (Real.cos θ * Real.cos φ * S 0) θ := by
      have := (Real.hasDerivAt_sin θ).mul_const (Real.cos φ * S 0); simp only [mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.cos x * Real.cos φ * S 1) (-Real.sin θ * Real.cos φ * S 1) θ := by
      have := (Real.hasDerivAt_cos θ).mul_const (Real.cos φ * S 1); simp only [mul_assoc, neg_mul] at this ⊢; exact this
    convert h1.sub h2 using 1; ring

private lemma hasDerivAt_rotMθ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθ θ φ' S) (rotMθφ θ φ S) φ := by
  have h_f : (fun φ' => rotMθ θ φ' S) = (fun φ' => !₂[-Real.cos θ * S 0 - Real.sin θ * S 1,
      Real.sin θ * Real.cos φ' * S 0 - Real.cos θ * Real.cos φ' * S 1]) := by
    ext φ' i; fin_cases i <;> simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMθφ θ φ S = !₂[(0 : ℝ), -Real.sin θ * Real.sin φ * S 0 + Real.cos θ * Real.sin φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => Real.sin θ * Real.cos x * S 0) (-Real.sin θ * Real.sin φ * S 0) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (Real.sin θ)).mul_const (S 0)
      simp only [neg_mul, mul_neg, mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.cos θ * Real.cos x * S 1) (-Real.cos θ * Real.sin φ * S 1) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (Real.cos θ)).mul_const (S 1)
      simp only [neg_mul, mul_neg, mul_assoc] at this ⊢; exact this
    convert h1.sub h2 using 1; ring

private lemma hasDerivAt_rotMφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMφ θ' φ S) (rotMθφ θ φ S) θ := by
  have h_f : (fun θ' => rotMφ θ' φ S) = (fun θ' => !₂[(0 : ℝ),
      Real.cos θ' * Real.sin φ * S 0 + Real.sin θ' * Real.sin φ * S 1 + Real.cos φ * S 2]) := by
    ext θ' i; fin_cases i <;> (simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMθφ θ φ S = !₂[(0 : ℝ), -Real.sin θ * Real.sin φ * S 0 + Real.cos θ * Real.sin φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => Real.cos x * Real.sin φ * S 0) (-Real.sin θ * Real.sin φ * S 0) θ := by
      have := (Real.hasDerivAt_cos θ).mul_const (Real.sin φ * S 0); simp only [mul_assoc, neg_mul] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin x * Real.sin φ * S 1) (Real.cos θ * Real.sin φ * S 1) θ := by
      have := (Real.hasDerivAt_sin θ).mul_const (Real.sin φ * S 1); simp only [mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun _ : ℝ => Real.cos φ * S 2) 0 θ := hasDerivAt_const _ _
    convert (h1.add h2).add h3 using 1; ring

private lemma hasDerivAt_rotMφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMφ θ φ' S) (rotMφφ θ φ S) φ := by
  have h_f : (fun φ' => rotMφ θ φ' S) = (fun φ' => !₂[(0 : ℝ),
      Real.cos θ * Real.sin φ' * S 0 + Real.sin θ * Real.sin φ' * S 1 + Real.cos φ' * S 2]) := by
    ext φ' i; fin_cases i <;> simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMφφ θ φ S = !₂[(0 : ℝ),
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1 - Real.sin φ * S 2] := by
    ext i; fin_cases i <;> simp [rotMφφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => Real.cos θ * Real.sin x * S 0) (Real.cos θ * Real.cos φ * S 0) φ := by
      have := ((Real.hasDerivAt_sin φ).const_mul (Real.cos θ)).mul_const (S 0)
      simp only [mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin θ * Real.sin x * S 1) (Real.sin θ * Real.cos φ * S 1) φ := by
      have := ((Real.hasDerivAt_sin φ).const_mul (Real.sin θ)).mul_const (S 1)
      simp only [mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun x => Real.cos x * S 2) (-Real.sin φ * S 2) φ := by
      have := (Real.hasDerivAt_cos φ).mul_const (S 2); simp only [neg_mul] at this ⊢; exact this
    convert (h1.add h2).add h3 using 1; ring

-- Helper lemmas for computing fderiv in coordinate directions
-- These show that fderiv f y (e_i) equals the partial derivative in direction i

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₀ gives rotR' -/
private lemma fderiv_rotR_rotM_in_e0 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 + t := by
    intro t
    simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      ↓reduceIte, smul_eq_mul, mul_one, add_comm]
  have h1 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 := by
    intro t
    simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have h2 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
    intro t
    simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (2 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
      (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 0 1) := by
    unfold HasLineDerivAt
    have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 0 1).ofLp 0)
        (rotM ((y + t • EuclideanSpace.single 0 1).ofLp 1)
             ((y + t • EuclideanSpace.single 0 1).ofLp 2) S) =
        rotR (y.ofLp 0 + t) (rotM (y.ofLp 1) (y.ofLp 2) S) := by
      intro t; rw [h0, h1, h2]
    simp_rw [hsimp]
    have hrotR : HasDerivAt (fun α => rotR α (rotM (y.ofLp 1) (y.ofLp 2) S))
        (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 0) := HasDerivAt_rotR _ _
    have hid : HasDerivAt (fun t : ℝ => y.ofLp 0 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (y.ofLp 0)
    have hrotR' : HasDerivAt (fun α => rotR α (rotM (y.ofLp 1) (y.ofLp 2) S))
        (rotR' (y.ofLp 0 + 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 0 + 0) := by
      simp only [add_zero]; exact hrotR
    have hcomp := hrotR'.scomp 0 hid
    simp only [one_smul, add_zero] at hcomp
    have heq_fun : ((fun α ↦ rotR α (rotM (y.ofLp 1) (y.ofLp 2) S)) ∘ HAdd.hAdd (y.ofLp 0)) =
        (fun t => rotR (y.ofLp 0 + t) (rotM (y.ofLp 1) (y.ofLp 2) S)) := by
      ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hcomp
    exact hcomp
  exact hline.lineDeriv

/-- fderiv of rotR with any M in direction e₀ gives rotR' -/
private lemma fderiv_rotR_any_M_in_e0 (S : Euc(3)) (y : E 3) (M : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 + t := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply, ↓reduceIte, smul_eq_mul, mul_one, add_comm]
  have h1 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply, show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have h2 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply, show (2 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
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

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₂ gives rotR ∘ rotMφ -/
private lemma fderiv_rotR_rotM_in_e2 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (0 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have h1 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have h2 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 + t := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      ↓reduceIte, smul_eq_mul, mul_one, add_comm]
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
      simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
    have hfinal := hcomp_deriv'.scomp 0 hid
    simp only [one_smul, add_zero] at hfinal
    have heq_fun : ((fun φ => rotR (y.ofLp 0) (rotM (y.ofLp 1) φ S)) ∘ HAdd.hAdd (y.ofLp 2)) =
        (fun t => rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2 + t) S)) := by ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hfinal; exact hfinal
  exact hline.lineDeriv

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₁ gives rotR ∘ rotMθ -/
private lemma fderiv_rotR_rotM_in_e1 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have h1 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 + t := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      ↓reduceIte, smul_eq_mul, mul_one, add_comm]
  have h2 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
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
      simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
    have hfinal := hcomp_deriv'.scomp 0 hid
    simp only [one_smul, add_zero] at hfinal
    have heq_fun : ((fun θ => rotR (y.ofLp 0) (rotM θ (y.ofLp 2) S)) ∘ HAdd.hAdd (y.ofLp 1)) =
        (fun t => rotR (y.ofLp 0) (rotM (y.ofLp 1 + t) (y.ofLp 2) S)) := by ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hfinal; exact hfinal
  exact hline.lineDeriv

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₀ gives -rotR -/
private lemma fderiv_rotR'_rotM_in_e0 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    -(rotR α (rotM θ φ S)) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 + t := by
    intro t
    simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      ↓reduceIte, smul_eq_mul, mul_one, add_comm]
  have h1 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 := by
    intro t
    simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have h2 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
    intro t
    simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (2 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
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
private lemma fderiv_rotR'_rotM_in_e1 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR' α (rotMθ θ φ S) := by
  rw [← hf_diff.lineDeriv_eq_fderiv]
  have h0 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  have h1 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 + t := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      ↓reduceIte, smul_eq_mul, mul_one, add_comm]
  have h2 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
    intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
      show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
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
      simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
    have hfinal := hcomp_deriv'.scomp 0 hid
    simp only [one_smul, add_zero] at hfinal
    have heq_fun : ((fun θ' => rotR' α (rotM θ' φ S)) ∘ HAdd.hAdd θ) =
        (fun t => rotR' α (rotM (θ + t) φ S)) := by ext t; simp only [Function.comp_apply]
    rw [heq_fun] at hfinal; exact hfinal
  exact hline.lineDeriv

/--
A measure of how far an inner-shadow vertex S can "stick out"
-/
noncomputable
def G (p : Pose) (ε : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.inner S, w⟫ - (ε * (|⟪p.rotR' (p.rotM₁ S), w⟫| + |⟪p.rotR (p.rotM₁θ S), w⟫| + |⟪p.rotR (p.rotM₁φ S), w⟫|)
  + 9 * ε^2 / 2)

/--
A measure of how far an outer-shadow vertex P can "reach" along w.
-/
noncomputable
def H (p : Pose) (ε : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ P, w⟫ + ε * (|⟪p.rotM₂θ P, w⟫| + |⟪p.rotM₂φ P, w⟫|) + 2 * ε^2

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
noncomputable
def maxH (p : Pose) (poly : GoodPoly) (ε : ℝ) (w : ℝ²) : ℝ :=
  poly.vertices.image (H p ε w) |>.max' <| by
    simp only [Finset.image_nonempty]
    exact poly.nonempty

/--
A compact way of saying "the pose satisfies the global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyehdron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure GlobalTheoremPrecondition (poly : GoodPoly) (p : Pose) (ε : ℝ) : Type where
  S : ℝ³
  S_in_poly : S ∈ poly.vertices
  w : ℝ²
  w_unit : ‖w‖ = 1
  exceeds : G p ε S w > maxH p poly ε w

noncomputable
def GlobalTheoremPrecondition.Sval
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) (q : Pose) : ℝ:=
    ⟪hp.w, q.inner hp.S⟫

theorem GlobalTheoremPrecondition.norm_S_le_one
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : ‖hp.S‖ ≤ 1 :=
  poly.vertex_radius_le_one hp.S hp.S_in_poly

theorem GlobalTheoremPrecondition.norm_S_gt_zero
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : 0 < ‖hp.S‖ :=
  poly.nontriv hp.S hp.S_in_poly

theorem GlobalTheoremPrecondition.norm_S_ne_zero
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : 0 ≠ ‖hp.S‖ :=
  ne_of_lt hp.norm_S_gt_zero

noncomputable
def imgInner (p : Pose) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.inner P⟫

noncomputable
def maxInner (p : Pose) (poly: GoodPoly) (w : ℝ²) : ℝ :=
  (imgInner p poly.vertices w).max' (by simp only [imgInner, Finset.image_nonempty]; exact poly.nonempty)

noncomputable
def imgOuter (p : Pose) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.outer P⟫

noncomputable
def maxOuter (p : Pose) (poly : GoodPoly) (w : ℝ²) : ℝ :=
  (imgOuter p poly.vertices w).max' (by simp only [imgOuter, Finset.image_nonempty]; exact poly.nonempty)

/--
This is where we use hull_scalar_prod. The text in [SY25] this corresponds to is:

"As noted before, Rupert’s condition and Lemma 18 imply in particular that
max_{P} ⟪ R(α) M(θ₁, φ₁), P, w ⟫ < max_{P} ⟪ M(θ₂, φ₂), P, w ⟫"
-/
theorem global_theorem_le_reasoning (p : Pose)
    (poly : GoodPoly)
    (h_rupert : RupertPose p (convexHull ℝ poly.vertices)) (w : ℝ²) :
    maxInner p poly w ≤ maxOuter p poly w
    := by
  simp only [maxInner]
  refine Finset.max'_le _ _ _ ?_
  intro y hy
  simp only [maxOuter, imgOuter]
  simp only [imgInner, Finset.mem_image] at hy
  obtain ⟨v, ⟨hv, hv'⟩⟩ := hy
  rw [← hv']
  clear hv'
  change ⟪w, p.inner v⟫ ≤ (poly.vertices.image (⟪w, p.outer ·⟫)).max' _
  convert_to ⟪w, p.inner v⟫ ≤ ((poly.vertices.image p.outer).image (⟪w, ·⟫)).max' (by
      simp only [Finset.image_nonempty]; exact poly.nonempty)
  · simp [Finset.image_image]; rfl
  let S := p.inner v
  let V := poly.vertices.image p.outer
  have Vne : V.Nonempty := by simp only [V, Finset.image_nonempty]; exact poly.nonempty
  change ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) _
  refine hull_scalar_prod V Vne S ?_ w
  simp only [Finset.coe_image, V, S]
  exact p.is_rupert_imp_inner_in_outer poly.vertices h_rupert v hv

lemma rotproj_inner_pose_eq {S : ℝ³} {w : ℝ²} (p : Pose) : rotproj_inner S w p.innerParams = ⟪p.inner S, w⟫ := by
  simp only [rotproj_inner, Pose.inner, innerProj, PoseLike.inner, Pose.innerParams,
             Matrix.cons_val_zero, Matrix.cons_val, AffineMap.coe_comp,
             LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]
  change _ = ⟪(proj_xyL ∘L rotRM p.θ₁ p.φ₁ p.α) S, w⟫
  rw [← projxy_rotRM_eq_rotprojRM]
  rfl

/--
This is the function that Theorem 17's proof calls `f`.
It always returns a unit vector.
-/
noncomputable
def GlobalTheoremPrecondition.fu {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ³ → ℝ :=
  rotproj_inner_unit pc.S pc.w

/--
This is an outer-shadow analog of `fu`
-/
noncomputable
def GlobalTheoremPrecondition.fu_outer {pbar : Pose} {ε : ℝ} {poly : GoodPoly} (P : ℝ³)
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ² → ℝ :=
  rotproj_outer_unit P pc.w

/--
This is the function that Theorem 17's proof calls `f`, but multiplied by ‖S‖.
-/
noncomputable
def GlobalTheoremPrecondition.f {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ³ → ℝ :=
  rotproj_inner pc.S pc.w

theorem f_pose_eq_sval {p pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.f p.innerParams = pc.Sval p := by
  simp [GlobalTheoremPrecondition.f, GlobalTheoremPrecondition.Sval]
  rw [rotproj_inner_pose_eq]
  apply real_inner_comm

theorem f_pose_eq_inner {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.f pbar.innerParams = ⟪pbar.inner pc.S, pc.w⟫ := by
  rw [f_pose_eq_sval, GlobalTheoremPrecondition.Sval, real_inner_comm]

theorem GlobalTheoremPrecondition.fu_pose_eq_outer {p pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    pc.fu_outer P p.outerParams * ‖P‖ = ⟪pc.w, p.outer P⟫ := by
  simp only [GlobalTheoremPrecondition.fu_outer, rotproj_outer_unit, Pose.outer, outerProj,
             PoseLike.outer, Pose.outerParams, Matrix.cons_val_zero, Matrix.cons_val,
             AffineMap.coe_comp, LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe,
             Function.comp_apply]
  by_cases hP : P = 0
  · simp [hP]
  · rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hP), Pose.proj_rm_eq_m, real_inner_comm]

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
  simp [rotMθ, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotMθ θ φ S) 1 = Real.sin θ * Real.cos φ * S 0 - Real.cos θ * Real.cos φ * S 1 := by
  simp [rotMθ, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMφ_apply_0 (θ φ : ℝ) (S : ℝ³) :
    (rotMφ θ φ S) 0 = 0 := by
  simp [rotMφ, Matrix.vecHead, Matrix.vecTail]

private lemma rotMφ_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotMφ θ φ S) 1 = Real.cos θ * Real.sin φ * S 0 + Real.sin θ * Real.sin φ * S 1 + Real.cos φ * S 2 := by
  simp [rotMφ, Matrix.vecHead, Matrix.vecTail]; ring

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

-- Bridging lemma: function application equals .ofLp for EuclideanSpace
private lemma euclidean_ofLp_eq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    v i = v.ofLp i := rfl

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

set_option maxHeartbeats 800000 in
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
    have hα : pbar.innerParams.ofLp 0 = pbar.α := by simp [Pose.innerParams]
    have hθ : pbar.innerParams.ofLp 1 = pbar.θ₁ := by simp [Pose.innerParams]
    have hφ : pbar.innerParams.ofLp 2 = pbar.φ₁ := by simp [Pose.innerParams]
    have hsinα : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 0))
        (Real.cos pbar.α • proj0) pbar.innerParams :=
      (Real.hasStrictDerivAt_sin pbar.α).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj0 hα.symm
    have hcosα : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.α) • proj0) pbar.innerParams :=
      (Real.hasStrictDerivAt_cos pbar.α).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj0 hα.symm
    have hsinθ : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 1))
        (Real.cos pbar.θ₁ • proj1) pbar.innerParams :=
      (Real.hasStrictDerivAt_sin pbar.θ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj1 hθ.symm
    have hcosθ : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 1))
        (-(Real.sin pbar.θ₁) • proj1) pbar.innerParams :=
      (Real.hasStrictDerivAt_cos pbar.θ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj1 hθ.symm
    have hsinφ : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 2))
        (Real.cos pbar.φ₁ • proj2) pbar.innerParams :=
      (Real.hasStrictDerivAt_sin pbar.φ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj2 hφ.symm
    have hcosφ : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 2))
        (-(Real.sin pbar.φ₁) • proj2) pbar.innerParams :=
      (Real.hasStrictDerivAt_cos pbar.φ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj2 hφ.symm
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
  -- Use hasStrictFDerivAt_piLp to decompose into components, then convert to hasFDerivAt
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  intro i
  fin_cases i
  · -- Component 0: f(θ, φ) = -sin θ * P[0] + cos θ * P[1] (only depends on θ)
    simp only [Fin.isValue]
    -- Rewrite function using component lemma
    have hfunc : (fun x : ℝ² => ((rotM (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun x => -Real.sin (x.ofLp 0) * P 0 + Real.cos (x.ofLp 0) * P 1 := by
      ext x
      exact rotM_component0 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    -- The derivative: d ↦ (-cos θ * P[0] - sin θ * P[1]) * d[0]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotM' pbar P) =
        ((-Real.cos pbar.θ₂ * P 0 - Real.sin pbar.θ₂ * P 1) • PiLp.proj 2 (fun _ => ℝ) 0) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Fin.isValue]
      -- Expand rotMθ and rotMφ at component 0
      simp only [rotMθ, rotMφ, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      -- Evaluate the matrix row entries: ![a, b, c] 2 = c
      rw [show ![-Real.cos pbar.θ₂, -Real.sin pbar.θ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![(0 : ℝ), 0, 0] (2 : Fin 3) = 0 from rfl]
      ring
    rw [hderiv]
    -- Now prove: HasStrictFDerivAt (fun x => -sin(x 0) * P 0 + cos(x 0) * P 1)
    --            ((c) • proj 0) pbar.outerParams
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
      simp only [rotMθ, rotMφ, LinearMap.coe_toContinuousLinearMap',
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
  simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_component1 (θ φ : ℝ) (P : ℝ³) :
    (rotMθ θ φ P) 1 = Real.sin θ * Real.cos φ * P 0 - Real.cos θ * Real.cos φ * P 1 := by
  simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]
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
      simp only [rotMθθ, rotMθφ, LinearMap.coe_toContinuousLinearMap',
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
      simp only [rotMθθ, rotMθφ, LinearMap.coe_toContinuousLinearMap',
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
  simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]

private lemma rotMφ_component1 (θ φ : ℝ) (P : ℝ³) :
    (rotMφ θ φ P) 1 = Real.cos θ * Real.sin φ * P 0 + Real.sin θ * Real.sin φ * P 1 + Real.cos φ * P 2 := by
  simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]
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
      simp only [rotMθφ, rotMφφ, LinearMap.coe_toContinuousLinearMap',
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
      simp only [rotMθφ, rotMφφ, LinearMap.coe_toContinuousLinearMap',
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

-- Composition norm bounds for inner projection second derivatives
-- All compositions have norm ≤ 1 since ‖rotR‖ = ‖rotR'‖ = 1 and ‖rotM*‖ ≤ 1
private lemma comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖A ∘L B‖ ≤ 1 := by
  calc ‖A ∘L B‖ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le A B
    _ ≤ 1 * 1 := by apply mul_le_mul hA hB (norm_nonneg _) (by linarith)
    _ = 1 := by ring

private lemma neg_comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖-(A ∘L B)‖ ≤ 1 := by
  rw [norm_neg]
  exact comp_norm_le_one hA hB

-- The second partial derivatives of the inner-rotM function
-- Each equals ⟪A S, w⟫ where A ∈ {rotMθθ, rotMθφ, rotMφφ}
-- These follow from differentiating rotM twice using hasDerivAt_rotMθ_θ etc.
private lemma second_partial_inner_rotM_outer (S : ℝ³) (w : ℝ²) (x : E 2) (i j : Fin 2) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x = ⟪A S, w⟫ := by
  -- Each pair (i, j) corresponds to a specific second derivative matrix
  -- (0, 0) → rotMθθ, (0, 1) → rotMθφ, (1, 0) → rotMθφ, (1, 1) → rotMφφ
  -- All have operator norm ≤ 1 by rotMθθ_norm_le_one, rotMθφ_norm_le_one, rotMφφ_norm_le_one
  fin_cases i <;> fin_cases j
  · -- (0, 0): uses rotMθθ
    refine ⟨rotMθθ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθθ_norm_le_one _ _, ?_⟩
    -- The second partial of ⟪rotM S, w⟫ w.r.t. (θ, θ) equals ⟪rotMθθ S, w⟫
    let θ := x.ofLp 0; let φ := x.ofLp 1
    -- First partial ∂/∂θ: (fun y => ⟪rotM y S, w⟫) → (fun y => ⟪rotMθ y S, w⟫)
    have hDiff : Differentiable ℝ (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) :=
      Differentiable.inner ℝ (Differentiable.rotM_outer S) (by fun_prop)
    -- First partial in direction e₀ gives ⟪rotMθ S, w⟫
    have hfirst : ∀ y : E 2, (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1) = ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      intro y
      have hInner := fderiv_inner_apply ℝ (Differentiable.rotM_outer S y) (differentiableAt_const w) (EuclideanSpace.single 0 1)
      rw [hInner]
      -- First term: fderiv of constant w is 0
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
      rw [hw.fderiv]
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add]
      -- Second term: fderiv of rotM in e₀ direction is rotMθ
      set pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩ with hpbar_def
      have hpbar : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hfderiv_rotM : fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) y = rotM' pbar S :=
        (HasFDerivAt.rotM_outer pbar S).fderiv ▸ congrArg _ hpbar.symm
      rw [hfderiv_rotM]
      -- rotM' pbar S (e₀) = rotMθ θ φ S since pbar.θ₂ = y.ofLp 0, pbar.φ₂ = y.ofLp 1
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
      -- Need to show: ⟪WithLp.toLp 2 ((Matrix.of ...).mulVec v), w⟫ = ⟪rotMθ S, w⟫
      -- The matrix has columns [rotMθ S, rotMφ S] and v = [1, 0], so mulVec gives rotMθ S
      congr 1
      ext i
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        EuclideanSpace.single_apply, ↓reduceIte, mul_one,
        show (1 : Fin 2) ≠ 0 from by decide, mul_zero, add_zero]
    -- The first partial function is y ↦ ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫
    -- Unfold and use the equality
    unfold nth_partial
    -- The goal has EuclideanSpace.single ⟨0, ⋯⟩ 1, we need to normalize to single 0 1
    show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) x) (EuclideanSpace.single 0 1) = ⟪rotMθθ (x.ofLp 0) (x.ofLp 1) S, w⟫
    have hinner_eq : (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) = fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := funext hfirst
    rw [show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) x) = (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
        from congrArg (fderiv ℝ · x) hinner_eq]
    -- Second partial: differentiate ⟪rotMθ S, w⟫ w.r.t. θ
    have hDiff2 : Differentiable ℝ (fun y : E 2 => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) := by
      apply Differentiable.inner ℝ
      · intro y; rw [differentiableAt_piLp]; intro i
        simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)
      · intro y; exact differentiableAt_const w
    -- The inner product with constant w: fderiv (⟪f ·, w⟫) x v = ⟪fderiv f x v, w⟫
    have hInner2 : (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x) (EuclideanSpace.single 0 1) =
        ⟪(fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x) (EuclideanSpace.single 0 1), w⟫ := by
      have hf_diff : DifferentiableAt ℝ (fun y : E 2 => rotMθ (y.ofLp 0) (y.ofLp 1) S) x := by
        rw [differentiableAt_piLp]; intro i
        simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)
      have hg_diff : DifferentiableAt ℝ (fun _ : E 2 => w) x := differentiableAt_const w
      have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff hg_diff (EuclideanSpace.single 0 1)
      -- Explicitly rewrite the constant derivative to 0
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
      rw [hw.fderiv] at heq
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
      exact heq
    rw [hInner2]
    -- Use HasFDerivAt.rotMθ_outer to compute the derivative
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    -- fderiv (rotMθ S) at x = rotMθ' pbar S
    have hfderiv_rotMθ : fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x = rotMθ' pbar S := by
      have h := HasFDerivAt.rotMθ_outer pbar S
      rw [hpbar] at h
      exact h.fderiv
    rw [hfderiv_rotMθ]
    -- rotMθ' pbar S (e₀) = rotMθθ θ φ S since e₀ = [1, 0] and the first column is rotMθθ
    simp only [rotMθ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
    -- The matrix has columns [rotMθθ S, rotMθφ S] and v = [1, 0], so mulVec gives rotMθθ S
    congr 1
    ext i
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply, ↓reduceIte, mul_one,
      show (1 : Fin 2) ≠ 0 from by decide, mul_zero, add_zero]
    -- θ = x.ofLp 0 and φ = x.ofLp 1 by definition
    rfl
  · -- (0, 1): uses rotMθφ (derivative of rotMφ w.r.t. θ)
    refine ⟨rotMθφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθφ_norm_le_one _ _, ?_⟩
    -- The second partial of ⟪rotM S, w⟫ w.r.t. (θ, φ) equals ⟪rotMθφ S, w⟫
    -- First partial ∂/∂φ gives ⟪rotMφ S, w⟫, then ∂/∂θ gives ⟪rotMθφ S, w⟫
    let θ := x.ofLp 0; let φ := x.ofLp 1
    have hDiff : Differentiable ℝ (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) :=
      Differentiable.inner ℝ (Differentiable.rotM_outer S) (by fun_prop)
    -- First partial in direction e₁ gives ⟪rotMφ S, w⟫
    have hfirst : ∀ y : E 2, (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1) = ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      intro y
      have hInner := fderiv_inner_apply ℝ (Differentiable.rotM_outer S y) (differentiableAt_const w) (EuclideanSpace.single 1 1)
      rw [hInner]
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
      rw [hw.fderiv]
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add]
      set pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩ with hpbar_def
      have hpbar : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hfderiv_rotM : fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) y = rotM' pbar S :=
        (HasFDerivAt.rotM_outer pbar S).fderiv ▸ congrArg _ hpbar.symm
      rw [hfderiv_rotM]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
      congr 1
      ext i
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        EuclideanSpace.single_apply, ↓reduceIte, mul_one,
        show (0 : Fin 2) ≠ 1 from by decide, mul_zero, zero_add]
    unfold nth_partial
    show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) x) (EuclideanSpace.single 0 1) = ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫
    have hinner_eq : (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) = fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := funext hfirst
    rw [show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) x) = (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
        from congrArg (fderiv ℝ · x) hinner_eq]
    -- Second partial: differentiate ⟪rotMφ S, w⟫ w.r.t. θ
    have hDiff2 : Differentiable ℝ (fun y : E 2 => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) := by
      apply Differentiable.inner ℝ
      · intro y; rw [differentiableAt_piLp]; intro i
        simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop
      · intro y; exact differentiableAt_const w
    have hInner2 : (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x) (EuclideanSpace.single 0 1) =
        ⟪(fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x) (EuclideanSpace.single 0 1), w⟫ := by
      have hf_diff : DifferentiableAt ℝ (fun y : E 2 => rotMφ (y.ofLp 0) (y.ofLp 1) S) x := by
        rw [differentiableAt_piLp]; intro i
        simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop
      have hg_diff : DifferentiableAt ℝ (fun _ : E 2 => w) x := differentiableAt_const w
      have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff hg_diff (EuclideanSpace.single 0 1)
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
      rw [hw.fderiv] at heq
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
      exact heq
    rw [hInner2]
    -- Use HasFDerivAt.rotMφ_outer to compute the derivative
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    have hfderiv_rotMφ : fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x = rotMφ' pbar S := by
      have h := HasFDerivAt.rotMφ_outer pbar S
      rw [hpbar] at h
      exact h.fderiv
    rw [hfderiv_rotMφ]
    -- rotMφ' pbar S (e₀) = rotMθφ θ φ S since e₀ = [1, 0] and the first column is rotMθφ
    simp only [rotMφ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
    congr 1
    ext i
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply, ↓reduceIte, mul_one,
      show (1 : Fin 2) ≠ 0 from by decide, mul_zero, add_zero]
    rfl
  · -- (1, 0): uses rotMθφ (derivative of rotMθ w.r.t. φ)
    refine ⟨rotMθφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθφ_norm_le_one _ _, ?_⟩
    -- The second partial of ⟪rotM S, w⟫ w.r.t. (φ, θ) equals ⟪rotMθφ S, w⟫
    -- First partial ∂/∂θ gives ⟪rotMθ S, w⟫, then ∂/∂φ gives ⟪rotMθφ S, w⟫
    let θ := x.ofLp 0; let φ := x.ofLp 1
    have hDiff : Differentiable ℝ (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) :=
      Differentiable.inner ℝ (Differentiable.rotM_outer S) (by fun_prop)
    -- First partial in direction e₀ gives ⟪rotMθ S, w⟫
    have hfirst : ∀ y : E 2, (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1) = ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      intro y
      have hInner := fderiv_inner_apply ℝ (Differentiable.rotM_outer S y) (differentiableAt_const w) (EuclideanSpace.single 0 1)
      rw [hInner]
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
      rw [hw.fderiv]
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add]
      set pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩ with hpbar_def
      have hpbar : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hfderiv_rotM : fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) y = rotM' pbar S :=
        (HasFDerivAt.rotM_outer pbar S).fderiv ▸ congrArg _ hpbar.symm
      rw [hfderiv_rotM]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
      congr 1
      ext i
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        EuclideanSpace.single_apply, ↓reduceIte, mul_one,
        show (1 : Fin 2) ≠ 0 from by decide, mul_zero, add_zero]
    unfold nth_partial
    show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) x) (EuclideanSpace.single 1 1) = ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫
    have hinner_eq : (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) = fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := funext hfirst
    rw [show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 0 1)) x) = (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
        from congrArg (fderiv ℝ · x) hinner_eq]
    -- Second partial: differentiate ⟪rotMθ S, w⟫ w.r.t. φ
    have hDiff2 : Differentiable ℝ (fun y : E 2 => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) := by
      apply Differentiable.inner ℝ
      · intro y; rw [differentiableAt_piLp]; intro i
        simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)
      · intro y; exact differentiableAt_const w
    have hInner2 : (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x) (EuclideanSpace.single 1 1) =
        ⟪(fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x) (EuclideanSpace.single 1 1), w⟫ := by
      have hf_diff : DifferentiableAt ℝ (fun y : E 2 => rotMθ (y.ofLp 0) (y.ofLp 1) S) x := by
        rw [differentiableAt_piLp]; intro i
        simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)
      have hg_diff : DifferentiableAt ℝ (fun _ : E 2 => w) x := differentiableAt_const w
      have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff hg_diff (EuclideanSpace.single 1 1)
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
      rw [hw.fderiv] at heq
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
      exact heq
    rw [hInner2]
    -- Use HasFDerivAt.rotMθ_outer to compute the derivative
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    have hfderiv_rotMθ : fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x = rotMθ' pbar S := by
      have h := HasFDerivAt.rotMθ_outer pbar S
      rw [hpbar] at h
      exact h.fderiv
    rw [hfderiv_rotMθ]
    -- rotMθ' pbar S (e₁) = rotMθφ θ φ S since e₁ = [0, 1] and the second column is rotMθφ
    simp only [rotMθ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
    congr 1
    ext i
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply, ↓reduceIte, mul_one,
      show (0 : Fin 2) ≠ 1 from by decide, mul_zero, zero_add]
    rfl
  · -- (1, 1): uses rotMφφ
    refine ⟨rotMφφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMφφ_norm_le_one _ _, ?_⟩
    -- The second partial of ⟪rotM S, w⟫ w.r.t. (φ, φ) equals ⟪rotMφφ S, w⟫
    -- First partial ∂/∂φ gives ⟪rotMφ S, w⟫, then ∂/∂φ again gives ⟪rotMφφ S, w⟫
    let θ := x.ofLp 0; let φ := x.ofLp 1
    have hDiff : Differentiable ℝ (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) :=
      Differentiable.inner ℝ (Differentiable.rotM_outer S) (by fun_prop)
    -- First partial in direction e₁ gives ⟪rotMφ S, w⟫
    have hfirst : ∀ y : E 2, (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1) = ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      intro y
      have hInner := fderiv_inner_apply ℝ (Differentiable.rotM_outer S y) (differentiableAt_const w) (EuclideanSpace.single 1 1)
      rw [hInner]
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
      rw [hw.fderiv]
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add]
      set pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩ with hpbar_def
      have hpbar : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hfderiv_rotM : fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) y = rotM' pbar S :=
        (HasFDerivAt.rotM_outer pbar S).fderiv ▸ congrArg _ hpbar.symm
      rw [hfderiv_rotM]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
      congr 1
      ext i
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        EuclideanSpace.single_apply, ↓reduceIte, mul_one,
        show (0 : Fin 2) ≠ 1 from by decide, mul_zero, zero_add]
    unfold nth_partial
    show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) x) (EuclideanSpace.single 1 1) = ⟪rotMφφ (x.ofLp 0) (x.ofLp 1) S, w⟫
    have hinner_eq : (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) = fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := funext hfirst
    rw [show (fderiv ℝ (fun y : E 2 => (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
        (EuclideanSpace.single 1 1)) x) = (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
        from congrArg (fderiv ℝ · x) hinner_eq]
    -- Second partial: differentiate ⟪rotMφ S, w⟫ w.r.t. φ
    have hDiff2 : Differentiable ℝ (fun y : E 2 => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) := by
      apply Differentiable.inner ℝ
      · intro y; rw [differentiableAt_piLp]; intro i
        simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop
      · intro y; exact differentiableAt_const w
    have hInner2 : (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x) (EuclideanSpace.single 1 1) =
        ⟪(fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x) (EuclideanSpace.single 1 1), w⟫ := by
      have hf_diff : DifferentiableAt ℝ (fun y : E 2 => rotMφ (y.ofLp 0) (y.ofLp 1) S) x := by
        rw [differentiableAt_piLp]; intro i
        simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases i
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop
      have hg_diff : DifferentiableAt ℝ (fun _ : E 2 => w) x := differentiableAt_const w
      have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff hg_diff (EuclideanSpace.single 1 1)
      have hw : HasFDerivAt (fun _ : E 2 ↦ w) (0 : E 2 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
      rw [hw.fderiv] at heq
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
      exact heq
    rw [hInner2]
    -- Use HasFDerivAt.rotMφ_outer to compute the derivative
    set pbar : Pose := ⟨0, θ, 0, φ, 0⟩ with hpbar_def
    have hpbar : pbar.outerParams = x := by ext i; fin_cases i <;> rfl
    have hfderiv_rotMφ : fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x = rotMφ' pbar S := by
      have h := HasFDerivAt.rotMφ_outer pbar S
      rw [hpbar] at h
      exact h.fderiv
    rw [hfderiv_rotMφ]
    -- rotMφ' pbar S (e₁) = rotMφφ θ φ S since e₁ = [0, 1] and the second column is rotMφφ
    simp only [rotMφ', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, hpbar_def]
    congr 1
    ext i
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply, ↓reduceIte, mul_one,
      show (0 : Fin 2) ≠ 1 from by decide, mul_zero, zero_add]
    rfl

-- The second partial derivatives of the inner-rotprojRM function (3 variables: α, θ, φ)
-- Each equals ⟪A S, w⟫ where A is a composition of rotation matrices with ‖A‖ ≤ 1
-- Variables: x 0 = α, x 1 = θ, x 2 = φ
-- rotprojRM θ φ α S = rotR α (rotM θ φ S)
-- Second partials:
--   (0,0): ∂²/∂α² → -rotR ∘ rotM (rotR'' = -rotR)
--   (0,1), (1,0): ∂²/∂α∂θ → rotR' ∘ rotMθ
--   (0,2), (2,0): ∂²/∂α∂φ → rotR' ∘ rotMφ
--   (1,1): ∂²/∂θ² → rotR ∘ rotMθθ
--   (1,2), (2,1): ∂²/∂θ∂φ → rotR ∘ rotMθφ
--   (2,2): ∂²/∂φ² → rotR ∘ rotMφφ
set_option maxHeartbeats 400000 in
private lemma second_partial_inner_rotM_inner (S : ℝ³) (w : ℝ²) (x : E 3) (i j : Fin 3) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (rotproj_inner S w)) x = ⟪A S, w⟫ := by
  -- The proof requires 9 case analyses similar to the outer case
  -- Each case shows the second partial is ⟪A S, w⟫ where A is a composition
  -- of rotR/rotR' with rotM/rotMθ/rotMφ/rotMθθ/rotMθφ/rotMφφ
  -- All such compositions have ‖A‖ ≤ 1 by comp_norm_le_one
  --
  -- Variables: x 0 = α, x 1 = θ, x 2 = φ (note: rotprojRM takes θ φ α)
  -- rotproj_inner S w x = ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫
  --                     = ⟪rotR (x 0) (rotM (x 1) (x 2) S), w⟫
  let α := x.ofLp 0; let θ := x.ofLp 1; let φ := x.ofLp 2
  fin_cases i <;> fin_cases j
  · -- (0, 0): ∂²/∂α² → -(rotR α ∘L rotM θ φ)
    -- rotR'' = -rotR, so the second α-derivative of rotR is -rotR
    refine ⟨-(rotR α ∘L rotM θ φ), ?_, ?_⟩
    · -- Norm bound: ‖-(rotR ∘L rotM)‖ ≤ 1
      exact neg_comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (le_of_eq (Bounding.rotM_norm_one θ φ))
    · -- The second partial equals ⟪-(rotR ∘L rotM) S, w⟫
      -- Normalize the fin_cases indices
      show nth_partial 0 (nth_partial 0 (rotproj_inner S w)) x = ⟪(-(rotR α ∘L rotM θ φ)) S, w⟫
      -- First partial ∂/∂α of ⟪rotR α (rotM θ φ S), w⟫ = ⟪rotR' α (rotM θ φ S), w⟫
      have hDiff : Differentiable ℝ (rotproj_inner S w) := Differentiable.rotproj_inner S w
      -- rotproj_inner S w x = ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫ = ⟪rotR (x 0) (rotM (x 1) (x 2) S), w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      -- First partial in direction e₀ gives ⟪rotR' α (rotM θ φ S), w⟫
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) =
          ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y
        rw [heq_rotproj]
        -- Use fderiv_inner_apply
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 0 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        -- d/de₀[rotR α (rotM θ φ S)] = rotR' α (rotM θ φ S) by HasDerivAt_rotR
        let proj0 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
        have hproj0 : HasFDerivAt (fun z : ℝ³ => z.ofLp 0) proj0 y :=
          (PiLp.hasStrictFDerivAt_apply 2 y 0).hasFDerivAt
        have hderiv_rotR : HasDerivAt (fun α' => rotR α' (rotM (y.ofLp 1) (y.ofLp 2) S))
            (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 0) :=
          HasDerivAt_rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)
        -- Compose using hasFDerivAt (toSpanSingleton) and then convert to smulRight form
        have hfderiv_rotR : HasFDerivAt (fun α' : ℝ => rotR α' (rotM (y.ofLp 1) (y.ofLp 2) S))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))) (y.ofLp 0) :=
          hderiv_rotR.hasFDerivAt
        have hcomp' : HasFDerivAt ((fun α' => rotR α' (rotM (y.ofLp 1) (y.ofLp 2) S)) ∘ (fun z : E 3 => z.ofLp 0))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) ∘L proj0) y :=
          hfderiv_rotR.comp y hproj0
        have heq_form : ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) ∘L proj0 =
            proj0.smulRight (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) := by
          ext x; simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
        have hcomp : HasFDerivAt (fun z : E 3 => rotR (z.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))
            (proj0.smulRight (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))) y := by
          rw [← heq_form]; exact hcomp'
        -- Show the full and restricted functions have the same fderiv in direction e₀
        -- In direction e₀ = [1, 0, 0], only the α component varies, so rotM is constant
        have heq_fderiv : (fderiv ℝ (fun z => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) (EuclideanSpace.single 0 1) =
            (fderiv ℝ (fun z => rotR (z.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) y) (EuclideanSpace.single 0 1) := by
          -- Both give rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)
          rw [hcomp.fderiv]
          simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
            EuclideanSpace.single_apply, ↓reduceIte, one_smul]
          -- The full function restricted to line y + t*e₀ equals the restricted function
          -- because rotM is constant along this line (only α changes)
          exact fderiv_rotR_rotM_in_e0 S y hf_diff
        rw [heq_fderiv, hcomp.fderiv]
        simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
          EuclideanSpace.single_apply, ↓reduceIte, one_smul]
      -- The function for the first partial is y ↦ ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1)) =
          fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      -- Second partial: d/dα⟪rotR' α v, w⟫ = ⟪-rotR α v, w⟫ where v = rotM θ φ S is constant in α
      -- Use fderiv_inner_apply to decompose
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 0 1) =
          ⟪(fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x)
            (EuclideanSpace.single 0 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR'_rotM S x
        have hg_diff : DifferentiableAt ℝ (fun _ : E 3 => w) x := differentiableAt_const w
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff hg_diff (EuclideanSpace.single 0 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
        exact heq
      rw [hInner2]
      -- Now compute fderiv (rotR' (·.ofLp 0) (rotM (·.ofLp 1) (·.ofLp 2) S)) at x in direction e₀
      -- Since direction e₀ = [1, 0, 0], this is the partial w.r.t. α
      -- d/dα(rotR' α v)|_{v = rotM θ φ S} = -rotR α v by HasDerivAt_rotR'
      have hfderiv_rotR' : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 0 1) = -(rotR α (rotM θ φ S)) := by
        let proj0 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
        have hproj0 : HasFDerivAt (fun x : ℝ³ => x.ofLp 0) proj0 x :=
          (PiLp.hasStrictFDerivAt_apply 2 x 0).hasFDerivAt
        have hderiv : HasDerivAt (fun α' => rotR' α' (rotM θ φ S)) (-(rotR α (rotM θ φ S))) α :=
          HasDerivAt_rotR' α (rotM θ φ S)
        have hfderiv : HasFDerivAt (fun α' : ℝ => rotR' α' (rotM θ φ S))
            (ContinuousLinearMap.toSpanSingleton ℝ (-(rotR α (rotM θ φ S)))) α :=
          hderiv.hasFDerivAt
        have hcomp : HasFDerivAt ((fun α' => rotR' α' (rotM θ φ S)) ∘ (fun y : E 3 => y.ofLp 0))
            (ContinuousLinearMap.toSpanSingleton ℝ (-(rotR α (rotM θ φ S))) ∘L proj0) x :=
          hfderiv.comp x hproj0
        have heq_form : ContinuousLinearMap.toSpanSingleton ℝ (-(rotR α (rotM θ φ S))) ∘L proj0 =
            proj0.smulRight (-(rotR α (rotM θ φ S))) := by
          ext y; simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
        -- Show full and restricted fderiv agree in e₀ direction
        have hf_diff' : DifferentiableAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR'_rotM S x
        have heq_fderiv : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 0 1) =
            (fderiv ℝ ((fun α' => rotR' α' (rotM θ φ S)) ∘ (fun y : E 3 => y.ofLp 0)) x) (EuclideanSpace.single 0 1) := by
          -- Both sides equal -(rotR α (rotM θ φ S))
          rw [fderiv_rotR'_rotM_in_e0 S x α θ φ rfl rfl rfl hf_diff', hcomp.fderiv, heq_form]
          simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
            EuclideanSpace.single_apply, ↓reduceIte, one_smul]
        rw [heq_fderiv, hcomp.fderiv, heq_form]
        simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
          EuclideanSpace.single_apply, ↓reduceIte, smul_neg, one_smul]
      rw [hfderiv_rotR']
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply, inner_neg_left, neg_neg]
  · -- (0, 1): ∂²/∂α∂θ → rotR' α ∘L rotMθ θ φ
    refine ⟨rotR' α ∘L rotMθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMθ_norm_le_one θ φ)
    · -- First partial in direction 1 (θ) gives ⟪rotR α (rotMθ θ φ S), w⟫
      -- Second partial in direction 0 (α) gives ⟪rotR' α (rotMθ θ φ S), w⟫
      show nth_partial 0 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMθ θ φ) S, w⟫
      have hDiff : Differentiable ℝ (rotproj_inner S w) := Differentiable.rotproj_inner S w
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      -- First partial in direction e₁ (θ direction): gives ⟪rotR α (rotMθ θ φ S), w⟫
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) =
          ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y
        -- Use HasFDerivAt.rotproj_inner which gives the fderiv as rotproj_inner'
        set pbar : Pose := ⟨y.ofLp 1, 0, y.ofLp 2, 0, y.ofLp 0⟩ with hpbar_def
        have hpbar : pbar.innerParams = y := by ext i; fin_cases i <;> rfl
        rw [← hpbar, (HasFDerivAt.rotproj_inner pbar S w).fderiv, hpbar]
        -- rotproj_inner' at e₁ gives ⟪pbar.rotR (pbar.rotM₁θ S), w⟫ = ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫
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
      -- Second partial in α direction: d/dα⟪rotR α v, w⟫ = ⟪rotR' α v, w⟫
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 0 1) =
          ⟪(fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x)
            (EuclideanSpace.single 0 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMθ S x
        have hg_diff : DifferentiableAt ℝ (fun _ : E 3 => w) x := differentiableAt_const w
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff hg_diff (EuclideanSpace.single 0 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
        exact heq
      rw [hInner2]
      -- d/de₀[rotR α (rotMθ θ φ S)] = rotR' α (rotMθ θ φ S)
      -- In direction e₀ = [1, 0, 0], only α changes, so d/de₀ = d/dα
      have hfderiv_rotR : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 0 1) = rotR' α (rotMθ θ φ S) := by
        -- The restricted function fun y => rotR (y.ofLp 0) (rotMθ θ φ S) has the same derivative in direction e₀
        -- because rotMθ is independent of y.ofLp 0
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
        -- The full function and restricted function agree in direction e₀
        have hdiff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMθ S x
        have heq_fderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 0 1) =
            (fderiv ℝ ((fun α' => rotR α' (rotMθ θ φ S)) ∘ (fun z : E 3 => z.ofLp 0)) x) (EuclideanSpace.single 0 1) := by
          -- Both sides equal rotR' α (rotMθ θ φ S)
          -- LHS via lineDeriv
          have hLHS : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 0 1) =
              rotR' α (rotMθ θ φ S) := by
            rw [← hdiff.lineDeriv_eq_fderiv]
            have h0 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = x.ofLp 0 + t := by
              intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply, ↓reduceIte, smul_eq_mul, mul_one, add_comm]
            have h1 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = x.ofLp 1 := by
              intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply, show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
            have h2 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = x.ofLp 2 := by
              intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply, show (2 : Fin 3) ≠ 0 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
            have hline : HasLineDerivAt ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S))
                (rotR' α (rotMθ θ φ S)) x (EuclideanSpace.single 0 1) := by
              unfold HasLineDerivAt
              have hsimp : ∀ t, rotR ((x + t • EuclideanSpace.single 0 1).ofLp 0) (rotMθ ((x + t • EuclideanSpace.single 0 1).ofLp 1) ((x + t • EuclideanSpace.single 0 1).ofLp 2) S) =
                  rotR (α + t) (rotMθ θ φ S) := by intro t; rw [h0, h1, h2]
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
          simp only [heq_form, ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply, EuclideanSpace.single_apply, ↓reduceIte, one_smul]
        rw [heq_fderiv, hcomp.fderiv]
        simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
          EuclideanSpace.single_apply, ↓reduceIte, one_smul]
      rw [hfderiv_rotR]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (0, 2): ∂²/∂α∂φ → rotR' α ∘L rotMφ θ φ
    refine ⟨rotR' α ∘L rotMφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMφ_norm_le_one θ φ)
    · -- First partial in direction 2 (φ) gives ⟪rotR α (rotMφ θ φ S), w⟫
      -- Second partial in direction 0 (α) gives ⟪rotR' α (rotMφ θ φ S), w⟫
      show nth_partial 0 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) =
          ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y
        rw [heq_rotproj]
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 2 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        let proj2 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
        have hproj2 : HasFDerivAt (fun z : ℝ³ => z.ofLp 2) proj2 y :=
          (PiLp.hasStrictFDerivAt_apply 2 y 2).hasFDerivAt
        have hderiv_rotMφ : HasDerivAt (fun φ' => rotM (y.ofLp 1) φ' S) (rotMφ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 2) :=
          hasDerivAt_rotM_φ (y.ofLp 1) (y.ofLp 2) S
        have hcomp : HasFDerivAt (fun z : E 3 => rotR (y.ofLp 0) (rotM (y.ofLp 1) (z.ofLp 2) S))
            (proj2.smulRight (rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S))) y := by
          -- Use HasDerivAt.hasFDerivAt + HasFDerivAt.comp pattern
          have hfderiv_rotM : HasFDerivAt (fun φ' : ℝ => rotM (y.ofLp 1) φ' S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 2) :=
            hderiv_rotMφ.hasFDerivAt
          have hM' : HasFDerivAt ((fun φ' => rotM (y.ofLp 1) φ' S) ∘ (fun z : E 3 => z.ofLp 2))
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMφ (y.ofLp 1) (y.ofLp 2) S) ∘L proj2) y :=
            hfderiv_rotM.comp y hproj2
          have heq_form : ContinuousLinearMap.toSpanSingleton ℝ (rotMφ (y.ofLp 1) (y.ofLp 2) S) ∘L proj2 =
              proj2.smulRight (rotMφ (y.ofLp 1) (y.ofLp 2) S) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
          have hM : HasFDerivAt (fun z : E 3 => rotM (y.ofLp 1) (z.ofLp 2) S)
              (proj2.smulRight (rotMφ (y.ofLp 1) (y.ofLp 2) S)) y := by rw [← heq_form]; exact hM'
          have hR : HasFDerivAt (fun v => rotR (y.ofLp 0) v)
              (rotR (y.ofLp 0)) (rotM (y.ofLp 1) (y.ofLp 2) S) := ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
          have hcomp := hR.comp y hM
          -- (rotR α).comp (proj2.smulRight v) = proj2.smulRight (rotR α v)
          have heq_comp : (rotR (y.ofLp 0)).comp (proj2.smulRight (rotMφ (y.ofLp 1) (y.ofLp 2) S)) =
              proj2.smulRight (rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) :=
            ContinuousLinearMap.ext fun z => (rotR (y.ofLp 0)).map_smul (proj2 z) (rotMφ (y.ofLp 1) (y.ofLp 2) S)
          rw [heq_comp] at hcomp; exact hcomp
        -- In direction e₂ = [0, 0, 1], only the φ component varies while α, θ are fixed
        have heq_fderiv : (fderiv ℝ (fun z => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) (EuclideanSpace.single 2 1) =
            (fderiv ℝ (fun z => rotR (y.ofLp 0) (rotM (y.ofLp 1) (z.ofLp 2) S)) y) (EuclideanSpace.single 2 1) := by
          rw [hcomp.fderiv]
          simp only [ContinuousLinearMap.smulRight_apply, proj2, PiLp.proj_apply,
            EuclideanSpace.single_apply, show (0 : Fin 3) ≠ 2 from by decide, show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte, one_smul]
          exact fderiv_rotR_rotM_in_e2 S y hf_diff
        rw [heq_fderiv, hcomp.fderiv]
        simp only [ContinuousLinearMap.smulRight_apply, proj2, PiLp.proj_apply,
          EuclideanSpace.single_apply, show (0 : Fin 3) ≠ 2 from by decide, show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte, one_smul]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 0 1) =
          ⟪(fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 0 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMφ S x
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff (differentiableAt_const w) (EuclideanSpace.single 0 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
        exact heq
      rw [hInner2]
      have hfderiv_rotR : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 0 1) = rotR' α (rotMφ θ φ S) := by
        let proj0 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
        have hproj0 : HasFDerivAt (fun x : ℝ³ => x.ofLp 0) proj0 x :=
          (PiLp.hasStrictFDerivAt_apply 2 x 0).hasFDerivAt
        have hderiv : HasDerivAt (fun α' => rotR α' (rotMφ θ φ S)) (rotR' α (rotMφ θ φ S)) α :=
          HasDerivAt_rotR α (rotMφ θ φ S)
        have hfderiv : HasFDerivAt (fun α' : ℝ => rotR α' (rotMφ θ φ S))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMφ θ φ S))) α :=
          hderiv.hasFDerivAt
        have hcomp' : HasFDerivAt ((fun α' => rotR α' (rotMφ θ φ S)) ∘ (fun y : E 3 => y.ofLp 0))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMφ θ φ S)) ∘L proj0) x :=
          hfderiv.comp x hproj0
        have heq_form : ContinuousLinearMap.toSpanSingleton ℝ (rotR' α (rotMφ θ φ S)) ∘L proj0 =
            proj0.smulRight (rotR' α (rotMφ θ φ S)) := by
          ext y; simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
        have hcomp : HasFDerivAt (fun y : E 3 => rotR (y.ofLp 0) (rotMφ θ φ S))
            (proj0.smulRight (rotR' α (rotMφ θ φ S))) x := by rw [← heq_form]; exact hcomp'
        -- Show full and restricted fderiv agree in e₀ direction
        have heq_fderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 0 1) =
            (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ θ φ S)) x) (EuclideanSpace.single 0 1) := by
          rw [hcomp.fderiv]
          simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
            EuclideanSpace.single_apply, ↓reduceIte, one_smul]
          exact fderiv_rotR_any_M_in_e0 S x rotMφ (differentiableAt_rotR_rotMφ S x)
        rw [heq_fderiv, hcomp.fderiv]
        simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
          EuclideanSpace.single_apply, ↓reduceIte, one_smul]
      rw [hfderiv_rotR]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (1, 0): ∂²/∂θ∂α → rotR' α ∘L rotMθ θ φ (same operator as (0,1))
    refine ⟨rotR' α ∘L rotMθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMθ_norm_le_one θ φ)
    · -- First partial in direction 0 (α) gives ⟪rotR' α (rotM θ φ S), w⟫
      -- Second partial in direction 1 (θ) gives ⟪rotR' α (rotMθ θ φ S), w⟫
      show nth_partial 1 (nth_partial 0 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMθ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) =
          ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y
        rw [heq_rotproj]
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 0 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        let proj0 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
        have hproj0 : HasFDerivAt (fun z : ℝ³ => z.ofLp 0) proj0 y :=
          (PiLp.hasStrictFDerivAt_apply 2 y 0).hasFDerivAt
        have hderiv_rotR : HasDerivAt (fun α' => rotR α' (rotM (y.ofLp 1) (y.ofLp 2) S))
            (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 0) :=
          HasDerivAt_rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)
        have hfderiv_rotR : HasFDerivAt (fun α' : ℝ => rotR α' (rotM (y.ofLp 1) (y.ofLp 2) S))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))) (y.ofLp 0) :=
          hderiv_rotR.hasFDerivAt
        have hcomp' : HasFDerivAt ((fun α' => rotR α' (rotM (y.ofLp 1) (y.ofLp 2) S)) ∘ (fun z : E 3 => z.ofLp 0))
            (ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) ∘L proj0) y :=
          hfderiv_rotR.comp y hproj0
        have heq_form : ContinuousLinearMap.toSpanSingleton ℝ (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) ∘L proj0 =
            proj0.smulRight (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) := by
          ext z; simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
        have hcomp : HasFDerivAt (fun z : E 3 => rotR (z.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))
            (proj0.smulRight (rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))) y := by rw [← heq_form]; exact hcomp'
        -- Show full and restricted fderiv agree in e₀ direction
        have heq_fderiv : (fderiv ℝ (fun z => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) (EuclideanSpace.single 0 1) =
            (fderiv ℝ (fun z => rotR (z.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) y) (EuclideanSpace.single 0 1) := by
          rw [hcomp.fderiv]
          simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
            EuclideanSpace.single_apply, ↓reduceIte, one_smul]
          exact fderiv_rotR_rotM_in_e0 S y hf_diff
        rw [heq_fderiv, hcomp.fderiv]
        simp only [ContinuousLinearMap.smulRight_apply, proj0, PiLp.proj_apply,
          EuclideanSpace.single_apply, ↓reduceIte, one_smul]
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1)) =
          fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 1 1) =
          ⟪(fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 1 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR'_rotM S x
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff (differentiableAt_const w) (EuclideanSpace.single 1 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq
        exact heq
      rw [hInner2]
      -- d/de₁[rotR' α (rotM θ φ S)] = rotR' α (rotMθ θ φ S) since rotR' is constant in θ
      have hfderiv : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 1 1) = rotR' α (rotMθ θ φ S) := by
        let proj1 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)
        have hproj1 : HasFDerivAt (fun z : ℝ³ => z.ofLp 1) proj1 x :=
          (PiLp.hasStrictFDerivAt_apply 2 x 1).hasFDerivAt
        have hderiv_rotM : HasDerivAt (fun θ' => rotM θ' φ S) (rotMθ θ φ S) θ := hasDerivAt_rotM_θ θ φ S
        have hcomp : HasFDerivAt (fun y : E 3 => rotR' α (rotM (y.ofLp 1) φ S))
            (proj1.smulRight (rotR' α (rotMθ θ φ S))) x := by
          -- Use HasDerivAt.hasFDerivAt + HasFDerivAt.comp pattern
          have hfderiv_rotM : HasFDerivAt (fun θ' : ℝ => rotM θ' φ S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ θ φ S)) θ := hderiv_rotM.hasFDerivAt
          have hM' : HasFDerivAt ((fun θ' => rotM θ' φ S) ∘ (fun z : E 3 => z.ofLp 1))
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ θ φ S) ∘L proj1) x :=
            hfderiv_rotM.comp x hproj1
          have heq_form_M : ContinuousLinearMap.toSpanSingleton ℝ (rotMθ θ φ S) ∘L proj1 =
              proj1.smulRight (rotMθ θ φ S) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
          have hM : HasFDerivAt (fun z : E 3 => rotM (z.ofLp 1) φ S) (proj1.smulRight (rotMθ θ φ S)) x := by
            rw [← heq_form_M]; exact hM'
          have hR : HasFDerivAt (fun v => rotR' α v) (rotR' α) (rotM θ φ S) := ContinuousLinearMap.hasFDerivAt (rotR' α)
          have hcomp := hR.comp x hM
          have heq_comp : (rotR' α).comp (proj1.smulRight (rotMθ θ φ S)) =
              proj1.smulRight (rotR' α (rotMθ θ φ S)) :=
            ContinuousLinearMap.ext fun z => (rotR' α).map_smul (proj1 z) (rotMθ θ φ S)
          rw [heq_comp] at hcomp; exact hcomp
        -- Show full and restricted fderiv agree in e₁ direction
        have heq_fderiv : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 1 1) =
            (fderiv ℝ (fun y => rotR' α (rotM (y.ofLp 1) φ S)) x) (EuclideanSpace.single 1 1) := by
          rw [hcomp.fderiv]
          simp only [ContinuousLinearMap.smulRight_apply, proj1, PiLp.proj_apply,
            EuclideanSpace.single_apply, show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, one_smul]
          exact fderiv_rotR'_rotM_in_e1 S x α θ φ rfl rfl rfl (differentiableAt_rotR'_rotM S x)
        rw [heq_fderiv, hcomp.fderiv]
        simp only [ContinuousLinearMap.smulRight_apply, proj1, PiLp.proj_apply,
          EuclideanSpace.single_apply, show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, one_smul]
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (1, 1): ∂²/∂θ² → rotR α ∘L rotMθθ θ φ
    refine ⟨rotR α ∘L rotMθθ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθθ_norm_le_one θ φ)
    · -- First partial in direction 1 (θ) gives ⟪rotR α (rotMθ θ φ S), w⟫
      -- Second partial in direction 1 (θ) gives ⟪rotR α (rotMθθ θ φ S), w⟫
      show nth_partial 1 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθθ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) =
          ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y
        rw [heq_rotproj]
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 1 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        -- Use lineDeriv to compute fderiv in direction e₁
        rw [← hf_diff.lineDeriv_eq_fderiv]
        have h0 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = y.ofLp 0 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h1 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = y.ofLp 1 + t := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            ↓reduceIte, smul_eq_mul, mul_one, add_comm]
        have h2 : ∀ t : ℝ, (y + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = y.ofLp 2 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have hline : HasLineDerivAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S))
            (rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) y (EuclideanSpace.single 1 1) := by
          unfold HasLineDerivAt
          have hsimp : ∀ t, rotR ((y + t • EuclideanSpace.single 1 1).ofLp 0)
              (rotM ((y + t • EuclideanSpace.single 1 1).ofLp 1) ((y + t • EuclideanSpace.single 1 1).ofLp 2) S) =
              rotR (y.ofLp 0) (rotM (y.ofLp 1 + t) (y.ofLp 2) S) := by intro t; rw [h0, h1, h2, add_comm]
          simp_rw [hsimp]
          have hrotM : HasDerivAt (fun θ' => rotM θ' (y.ofLp 2) S) (rotMθ (y.ofLp 1) (y.ofLp 2) S) (y.ofLp 1) :=
            hasDerivAt_rotM_θ _ _ _
          have hR' : HasFDerivAt (fun v => rotR (y.ofLp 0) v) (rotR (y.ofLp 0)) (rotM (y.ofLp 1) (y.ofLp 2) S) :=
            ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))
          have hrotM_fderiv : HasFDerivAt (fun θ' : ℝ => rotM θ' (y.ofLp 2) S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 1) := hrotM.hasFDerivAt
          have hcomp_inner := hR'.comp (y.ofLp 1) hrotM_fderiv
          have heq_comp' : (rotR (y.ofLp 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθ (y.ofLp 1) (y.ofLp 2) S)) =
              ContinuousLinearMap.toSpanSingleton ℝ (rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
          rw [heq_comp'] at hcomp_inner
          have hcomp_deriv : HasDerivAt ((fun v => rotR (y.ofLp 0) v) ∘ (fun θ' => rotM θ' (y.ofLp 2) S))
              (rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) (y.ofLp 1) := by
            have h := hcomp_inner.hasDerivAt (x := y.ofLp 1)
            simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h; exact h
          have hid : HasDerivAt (fun t : ℝ => y.ofLp 1 + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add (y.ofLp 1)
          have hcomp_deriv' : HasDerivAt (fun θ' => rotR (y.ofLp 0) (rotM θ' (y.ofLp 2) S))
              (rotR (y.ofLp 0) (rotMθ (y.ofLp 1 + 0) (y.ofLp 2) S)) (y.ofLp 1 + 0) := by
            simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
          have hfinal := hcomp_deriv'.scomp 0 hid
          simp only [one_smul, add_zero] at hfinal
          have heq_fun : ((fun θ' => rotR (y.ofLp 0) (rotM θ' (y.ofLp 2) S)) ∘ HAdd.hAdd (y.ofLp 1)) =
              (fun t => rotR (y.ofLp 0) (rotM (y.ofLp 1 + t) (y.ofLp 2) S)) := by ext t; simp only [Function.comp_apply]
          rw [heq_fun] at hfinal; exact hfinal
        exact congrArg (⟪·, w⟫) hline.lineDeriv
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 1 1) =
          ⟪(fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 1 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMθ S x
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff (differentiableAt_const w) (EuclideanSpace.single 1 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq; exact heq
      rw [hInner2]
      -- Second partial: in direction e₁, rotR α is constant, so d/dθ[rotR α (rotMθ θ φ S)] = rotR α (rotMθθ θ φ S)
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 1 1) = rotR α (rotMθθ θ φ S) := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMθ S x
        rw [← hf_diff.lineDeriv_eq_fderiv]
        have h0 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = x.ofLp 0 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h1 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = x.ofLp 1 + t := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            ↓reduceIte, smul_eq_mul, mul_one, add_comm]
        have h2 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = x.ofLp 2 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have hline : HasLineDerivAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S))
            (rotR α (rotMθθ θ φ S)) x (EuclideanSpace.single 1 1) := by
          unfold HasLineDerivAt
          have hsimp : ∀ t, rotR ((x + t • EuclideanSpace.single 1 1).ofLp 0)
              (rotMθ ((x + t • EuclideanSpace.single 1 1).ofLp 1) ((x + t • EuclideanSpace.single 1 1).ofLp 2) S) =
              rotR α (rotMθ (θ + t) φ S) := by intro t; rw [h0, h1, h2, add_comm]
          simp_rw [hsimp]
          have hrotMθ : HasDerivAt (fun θ' => rotMθ θ' φ S) (rotMθθ θ φ S) θ := hasDerivAt_rotMθ_θ θ φ S
          have hR : HasFDerivAt (fun v => rotR α v) (rotR α) (rotMθ θ φ S) := ContinuousLinearMap.hasFDerivAt (rotR α)
          have hrotMθ_fderiv : HasFDerivAt (fun θ' : ℝ => rotMθ θ' φ S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMθθ θ φ S)) θ := hrotMθ.hasFDerivAt
          have hcomp_inner := hR.comp θ hrotMθ_fderiv
          have heq_comp : (rotR α).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθθ θ φ S)) =
              ContinuousLinearMap.toSpanSingleton ℝ (rotR α (rotMθθ θ φ S)) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
          rw [heq_comp] at hcomp_inner
          have hcomp_deriv : HasDerivAt ((fun v => rotR α v) ∘ (fun θ' => rotMθ θ' φ S))
              (rotR α (rotMθθ θ φ S)) θ := by
            have h := hcomp_inner.hasDerivAt (x := θ)
            simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h; exact h
          have hid : HasDerivAt (fun t : ℝ => θ + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add θ
          have hcomp_deriv' : HasDerivAt (fun θ' => rotR α (rotMθ θ' φ S)) (rotR α (rotMθθ (θ + 0) φ S)) (θ + 0) := by
            simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
          have hfinal := hcomp_deriv'.scomp 0 hid
          simp only [one_smul, add_zero] at hfinal
          have heq_fun : ((fun θ' => rotR α (rotMθ θ' φ S)) ∘ HAdd.hAdd θ) =
              (fun t => rotR α (rotMθ (θ + t) φ S)) := by ext t; simp only [Function.comp_apply]
          rw [heq_fun] at hfinal; exact hfinal
        exact hline.lineDeriv
      rw [hfderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (1, 2): ∂²/∂θ∂φ → rotR α ∘L rotMθφ θ φ
    refine ⟨rotR α ∘L rotMθφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθφ_norm_le_one θ φ)
    · -- First partial in direction 2 (φ) gives ⟪rotR α (rotMφ θ φ S), w⟫
      -- Second partial in direction 1 (θ) gives ⟪rotR α (rotMθφ θ φ S), w⟫
      show nth_partial 1 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) =
          ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 2 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        exact congrArg (⟪·, w⟫) (fderiv_rotR_rotM_in_e2 S y hf_diff)
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 1 1) =
          ⟪(fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 1 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMφ S x
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff (differentiableAt_const w) (EuclideanSpace.single 1 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq; exact heq
      rw [hInner2]
      -- d/dθ[rotR α (rotMφ θ φ S)] = rotR α (rotMθφ θ φ S) since rotR α is linear and rotMφ_θ = rotMθφ
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 1 1) = rotR α (rotMθφ θ φ S) := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMφ S x
        rw [← hf_diff.lineDeriv_eq_fderiv]
        have h0 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = x.ofLp 0 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (0 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h1 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = x.ofLp 1 + t := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            ↓reduceIte, smul_eq_mul, mul_one, add_comm]
        have h2 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = x.ofLp 2 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have hline : HasLineDerivAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S))
            (rotR α (rotMθφ θ φ S)) x (EuclideanSpace.single 1 1) := by
          unfold HasLineDerivAt
          have hsimp : ∀ t, rotR ((x + t • EuclideanSpace.single 1 1).ofLp 0)
              (rotMφ ((x + t • EuclideanSpace.single 1 1).ofLp 1) ((x + t • EuclideanSpace.single 1 1).ofLp 2) S) =
              rotR α (rotMφ (θ + t) φ S) := by intro t; rw [h0, h1, h2, add_comm]
          simp_rw [hsimp]
          have hrotMφ : HasDerivAt (fun θ' => rotMφ θ' φ S) (rotMθφ θ φ S) θ := hasDerivAt_rotMφ_θ θ φ S
          have hR : HasFDerivAt (fun v => rotR α v) (rotR α) (rotMφ θ φ S) := ContinuousLinearMap.hasFDerivAt (rotR α)
          have hrotMφ_fderiv : HasFDerivAt (fun θ' : ℝ => rotMφ θ' φ S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMθφ θ φ S)) θ := hrotMφ.hasFDerivAt
          have hcomp_inner := hR.comp θ hrotMφ_fderiv
          have heq_comp : (rotR α).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθφ θ φ S)) =
              ContinuousLinearMap.toSpanSingleton ℝ (rotR α (rotMθφ θ φ S)) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
          rw [heq_comp] at hcomp_inner
          have hcomp_deriv : HasDerivAt ((fun v => rotR α v) ∘ (fun θ' => rotMφ θ' φ S)) (rotR α (rotMθφ θ φ S)) θ := by
            have h := hcomp_inner.hasDerivAt (x := θ)
            simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h; exact h
          have hid : HasDerivAt (fun t : ℝ => θ + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add θ
          have hcomp_deriv' : HasDerivAt (fun θ' => rotR α (rotMφ θ' φ S)) (rotR α (rotMθφ (θ + 0) φ S)) (θ + 0) := by
            simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
          have hfinal := hcomp_deriv'.scomp 0 hid
          simp only [one_smul, add_zero] at hfinal
          have heq_fun : ((fun θ' => rotR α (rotMφ θ' φ S)) ∘ HAdd.hAdd θ) =
              (fun t => rotR α (rotMφ (θ + t) φ S)) := by ext t; simp only [Function.comp_apply]
          rw [heq_fun] at hfinal; exact hfinal
        exact hline.lineDeriv
      rw [hfderiv]; simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (2, 0): ∂²/∂φ∂α → rotR' α ∘L rotMφ θ φ (same as (0,2) by symmetry)
    refine ⟨rotR' α ∘L rotMφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one α)) (Bounding.rotMφ_norm_le_one θ φ)
    · -- First partial in direction 0 (α) gives ⟪rotR' α (rotM θ φ S), w⟫
      -- Second partial in direction 2 (φ) gives ⟪rotR' α (rotMφ θ φ S), w⟫
      show nth_partial 2 (nth_partial 0 (rotproj_inner S w)) x = ⟪(rotR' α ∘L rotMφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) =
          ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 0 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        exact congrArg (⟪·, w⟫) (fderiv_rotR_rotM_in_e0 S y hf_diff)
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1)) =
          fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 2 1) =
          ⟪(fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 2 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR'_rotM S x
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff (differentiableAt_const w) (EuclideanSpace.single 2 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq; exact heq
      rw [hInner2]
      -- d/dφ[rotR' α (rotM θ φ S)] = rotR' α (rotMφ θ φ S) since rotR' α is linear
      have hfderiv : (fderiv ℝ (fun y => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 2 1) = rotR' α (rotMφ θ φ S) := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR'_rotM S x
        rw [← hf_diff.lineDeriv_eq_fderiv]
        have h0 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = x.ofLp 0 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (0 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h1 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = x.ofLp 1 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h2 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = x.ofLp 2 + t := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            ↓reduceIte, smul_eq_mul, mul_one, add_comm]
        have hline : HasLineDerivAt ℝ (fun y : E 3 => rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S))
            (rotR' α (rotMφ θ φ S)) x (EuclideanSpace.single 2 1) := by
          unfold HasLineDerivAt
          have hsimp : ∀ t, rotR' ((x + t • EuclideanSpace.single 2 1).ofLp 0)
              (rotM ((x + t • EuclideanSpace.single 2 1).ofLp 1) ((x + t • EuclideanSpace.single 2 1).ofLp 2) S) =
              rotR' α (rotM θ (φ + t) S) := by intro t; rw [h0, h1, h2, add_comm]
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
            simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
          have hfinal := hcomp_deriv'.scomp 0 hid
          simp only [one_smul, add_zero] at hfinal
          have heq_fun : ((fun φ' => rotR' α (rotM θ φ' S)) ∘ HAdd.hAdd φ) =
              (fun t => rotR' α (rotM θ (φ + t) S)) := by ext t; simp only [Function.comp_apply]
          rw [heq_fun] at hfinal; exact hfinal
        exact hline.lineDeriv
      rw [hfderiv]; simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (2, 1): ∂²/∂φ∂θ → rotR α ∘L rotMθφ θ φ (same as (1,2) by symmetry)
    refine ⟨rotR α ∘L rotMθφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMθφ_norm_le_one θ φ)
    · -- First partial in direction 1 (θ) gives ⟪rotR α (rotMθ θ φ S), w⟫
      -- Second partial in direction 2 (φ) gives ⟪rotR α (rotMθφ θ φ S), w⟫
      show nth_partial 2 (nth_partial 1 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMθφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) =
          ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 1 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        exact congrArg (⟪·, w⟫) (fderiv_rotR_rotM_in_e1 S y hf_diff)
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 2 1) =
          ⟪(fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 2 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMθ S x
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff (differentiableAt_const w) (EuclideanSpace.single 2 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq; exact heq
      rw [hInner2]
      -- d/dφ[rotR α (rotMθ θ φ S)] = rotR α (rotMθφ θ φ S) since rotR α is linear
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 2 1) = rotR α (rotMθφ θ φ S) := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMθ S x
        rw [← hf_diff.lineDeriv_eq_fderiv]
        have h0 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = x.ofLp 0 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (0 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h1 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = x.ofLp 1 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h2 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = x.ofLp 2 + t := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            ↓reduceIte, smul_eq_mul, mul_one, add_comm]
        have hline : HasLineDerivAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S))
            (rotR α (rotMθφ θ φ S)) x (EuclideanSpace.single 2 1) := by
          unfold HasLineDerivAt
          have hsimp : ∀ t, rotR ((x + t • EuclideanSpace.single 2 1).ofLp 0)
              (rotMθ ((x + t • EuclideanSpace.single 2 1).ofLp 1) ((x + t • EuclideanSpace.single 2 1).ofLp 2) S) =
              rotR α (rotMθ θ (φ + t) S) := by intro t; rw [h0, h1, h2, add_comm]
          simp_rw [hsimp]
          have hrotMθ : HasDerivAt (fun φ' => rotMθ θ φ' S) (rotMθφ θ φ S) φ := hasDerivAt_rotMθ_φ θ φ S
          have hR : HasFDerivAt (fun v => rotR α v) (rotR α) (rotMθ θ φ S) := ContinuousLinearMap.hasFDerivAt (rotR α)
          have hrotMθ_fderiv : HasFDerivAt (fun φ' : ℝ => rotMθ θ φ' S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMθφ θ φ S)) φ := hrotMθ.hasFDerivAt
          have hcomp_inner := hR.comp φ hrotMθ_fderiv
          have heq_comp : (rotR α).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMθφ θ φ S)) =
              ContinuousLinearMap.toSpanSingleton ℝ (rotR α (rotMθφ θ φ S)) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
          rw [heq_comp] at hcomp_inner
          have hcomp_deriv : HasDerivAt ((fun v => rotR α v) ∘ (fun φ' => rotMθ θ φ' S)) (rotR α (rotMθφ θ φ S)) φ := by
            have h := hcomp_inner.hasDerivAt (x := φ)
            simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h; exact h
          have hid : HasDerivAt (fun t : ℝ => φ + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add φ
          have hcomp_deriv' : HasDerivAt (fun φ' => rotR α (rotMθ θ φ' S)) (rotR α (rotMθφ θ (φ + 0) S)) (φ + 0) := by
            simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
          have hfinal := hcomp_deriv'.scomp 0 hid
          simp only [one_smul, add_zero] at hfinal
          have heq_fun : ((fun φ' => rotR α (rotMθ θ φ' S)) ∘ HAdd.hAdd φ) =
              (fun t => rotR α (rotMθ θ (φ + t) S)) := by ext t; simp only [Function.comp_apply]
          rw [heq_fun] at hfinal; exact hfinal
        exact hline.lineDeriv
      rw [hfderiv]; simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · -- (2, 2): ∂²/∂φ² → rotR α ∘L rotMφφ θ φ
    refine ⟨rotR α ∘L rotMφφ θ φ, ?_, ?_⟩
    · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one α)) (Bounding.rotMφφ_norm_le_one θ φ)
    · -- First partial in direction 2 (φ) gives ⟪rotR α (rotMφ θ φ S), w⟫
      -- Second partial in direction 2 (φ) gives ⟪rotR α (rotMφφ θ φ S), w⟫
      show nth_partial 2 (nth_partial 2 (rotproj_inner S w)) x = ⟪(rotR α ∘L rotMφφ θ φ) S, w⟫
      have heq_rotproj : rotproj_inner S w = fun y => ⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        ext y; simp [rotproj_inner, rotprojRM]
      have hfirst : ∀ y : E 3, (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) =
          ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
        intro y; rw [heq_rotproj]
        have hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y :=
          differentiableAt_rotR_rotM S y
        have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (EuclideanSpace.single 2 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) y := hasFDerivAt_const w y
        rw [hw.fderiv] at hInner; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
        rw [hInner]
        exact congrArg (⟪·, w⟫) (fderiv_rotR_rotM_in_e2 S y hf_diff)
      unfold nth_partial
      have hinner_eq : (fun y : E 3 => (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1)) =
          fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := funext hfirst
      rw [congrArg (fderiv ℝ · x) hinner_eq]
      have hInner2 : (fderiv ℝ (fun y => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x)
          (EuclideanSpace.single 2 1) =
          ⟪(fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x) (EuclideanSpace.single 2 1), w⟫ := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMφ S x
        have heq := fderiv_inner_apply (𝕜 := ℝ) hf_diff (differentiableAt_const w) (EuclideanSpace.single 2 1)
        have hw : HasFDerivAt (fun _ : E 3 ↦ w) (0 : E 3 →L[ℝ] ℝ²) x := hasFDerivAt_const w x
        rw [hw.fderiv] at heq; simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at heq; exact heq
      rw [hInner2]
      -- d/dφ[rotR α (rotMφ θ φ S)] = rotR α (rotMφφ θ φ S) since rotR α is linear
      have hfderiv : (fderiv ℝ (fun y => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x)
          (EuclideanSpace.single 2 1) = rotR α (rotMφφ θ φ S) := by
        have hf_diff : DifferentiableAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S)) x :=
          differentiableAt_rotR_rotMφ S x
        rw [← hf_diff.lineDeriv_eq_fderiv]
        have h0 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 0 = x.ofLp 0 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (0 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h1 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 1 = x.ofLp 1 := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            show (1 : Fin 3) ≠ 2 from by decide, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
        have h2 : ∀ t : ℝ, (x + t • (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E 3)).ofLp 2 = x.ofLp 2 + t := by
          intro t; simp only [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, Pi.single_apply,
            ↓reduceIte, smul_eq_mul, mul_one, add_comm]
        have hline : HasLineDerivAt ℝ (fun y : E 3 => rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S))
            (rotR α (rotMφφ θ φ S)) x (EuclideanSpace.single 2 1) := by
          unfold HasLineDerivAt
          have hsimp : ∀ t, rotR ((x + t • EuclideanSpace.single 2 1).ofLp 0)
              (rotMφ ((x + t • EuclideanSpace.single 2 1).ofLp 1) ((x + t • EuclideanSpace.single 2 1).ofLp 2) S) =
              rotR α (rotMφ θ (φ + t) S) := by intro t; rw [h0, h1, h2, add_comm]
          simp_rw [hsimp]
          have hrotMφ : HasDerivAt (fun φ' => rotMφ θ φ' S) (rotMφφ θ φ S) φ := hasDerivAt_rotMφ_φ θ φ S
          have hR : HasFDerivAt (fun v => rotR α v) (rotR α) (rotMφ θ φ S) := ContinuousLinearMap.hasFDerivAt (rotR α)
          have hrotMφ_fderiv : HasFDerivAt (fun φ' : ℝ => rotMφ θ φ' S)
              (ContinuousLinearMap.toSpanSingleton ℝ (rotMφφ θ φ S)) φ := hrotMφ.hasFDerivAt
          have hcomp_inner := hR.comp φ hrotMφ_fderiv
          have heq_comp : (rotR α).comp (ContinuousLinearMap.toSpanSingleton ℝ (rotMφφ θ φ S)) =
              ContinuousLinearMap.toSpanSingleton ℝ (rotR α (rotMφφ θ φ S)) := by
            ext z; simp [ContinuousLinearMap.toSpanSingleton_apply]
          rw [heq_comp] at hcomp_inner
          have hcomp_deriv : HasDerivAt ((fun v => rotR α v) ∘ (fun φ' => rotMφ θ φ' S)) (rotR α (rotMφφ θ φ S)) φ := by
            have h := hcomp_inner.hasDerivAt (x := φ)
            simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h; exact h
          have hid : HasDerivAt (fun t : ℝ => φ + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add φ
          have hcomp_deriv' : HasDerivAt (fun φ' => rotR α (rotMφ θ φ' S)) (rotR α (rotMφφ θ (φ + 0) S)) (φ + 0) := by
            simp only [add_zero, Function.comp_apply] at hcomp_deriv ⊢; exact hcomp_deriv
          have hfinal := hcomp_deriv'.scomp 0 hid
          simp only [one_smul, add_zero] at hfinal
          have heq_fun : ((fun φ' => rotR α (rotMφ θ φ' S)) ∘ HAdd.hAdd φ) =
              (fun t => rotR α (rotMφ θ (φ + t) S)) := by ext t; simp only [Function.comp_apply]
          rw [heq_fun] at hfinal; exact hfinal
        exact hline.lineDeriv
      rw [hfderiv]; simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]

/- [SY25] Lemma 19 -/
theorem rotation_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_inner_unit S w) := by
  -- First handle the case when ‖S‖ = 0
  by_cases hS : ‖S‖ = 0
  · -- When ‖S‖ = 0, the function is constantly 0
    intro x i j
    have hzero : rotproj_inner_unit S w = 0 := by ext y; simp [rotproj_inner_unit, hS]
    have h1 : nth_partial j (rotproj_inner_unit S w) = 0 := by
      ext y
      simp only [nth_partial, hzero]
      rw [fderiv_zero]
      simp
    simp only [nth_partial, h1]
    rw [fderiv_zero]
    simp
  · -- When ‖S‖ ≠ 0, we have S_nonzero : ‖S‖ > 0
    have S_pos : ‖S‖ > 0 := (norm_nonneg S).lt_of_ne' hS
    intro x i j
    -- The function is rotproj_inner_unit S w = (rotproj_inner S w) / ‖S‖
    -- Its second partial equals (second partial of inner product) / ‖S‖
    -- By second_partial_inner_rotM_inner, the second partial of rotproj_inner is ⟪A S, w⟫
    -- where ‖A‖ ≤ 1, so the full second partial is ⟪A S, w⟫ / ‖S‖
    -- By inner_bound_helper, this has absolute value ≤ 1

    have heq : rotproj_inner_unit S w = fun y => rotproj_inner S w y / ‖S‖ := by
      ext y; rfl

    -- The function rotproj_inner is smooth (it's ‖S‖ times rotproj_inner_unit which is ContDiff ℝ 2)
    have hf_smooth : ContDiff ℝ 2 (rotproj_inner S w) := by
      have heq_inner : rotproj_inner S w = ‖S‖ • rotproj_inner_unit S w := by
        ext x; simp [rotproj_inner, rotproj_inner_unit, mul_div_cancel₀ _ (ne_of_gt S_pos)]
      rw [heq_inner]
      have h2 : ContDiff ℝ 2 (rotproj_inner_unit S w) := rotation_partials_exist S_pos
      exact contDiff_const.smul h2

    -- The second partial of f/‖S‖ is (second partial of f) / ‖S‖
    have hscale : nth_partial i (nth_partial j (rotproj_inner_unit S w)) x =
        nth_partial i (nth_partial j (rotproj_inner S w)) x / ‖S‖ := by
      -- rotproj_inner_unit S w = f / ‖S‖ where f = rotproj_inner S w
      -- nth_partial is ℝ-linear, so nth_partial(f/c) = nth_partial(f)/c
      rw [heq]
      -- The function f/‖S‖ can be written as ‖S‖⁻¹ • f
      have hdiv : (fun y => rotproj_inner S w y / ‖S‖) = ‖S‖⁻¹ • (rotproj_inner S w) := by
        ext y; simp [div_eq_inv_mul, smul_eq_mul]
      rw [hdiv]
      -- First application: nth_partial j (c • f) = c • nth_partial j f
      have hpartial_smul : nth_partial j (‖S‖⁻¹ • rotproj_inner S w) =
          ‖S‖⁻¹ • nth_partial j (rotproj_inner S w) := by
        ext y
        simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
        have h2ne : (2 : WithTop ℕ∞) ≠ 0 := by decide
        rw [fderiv_const_smul (c := ‖S‖⁻¹) (hf_smooth.differentiable h2ne y)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hpartial_smul]
      -- g = nth_partial j (rotproj_inner S w) is also smooth (ContDiff ℝ 1)
      have hg : ContDiff ℝ 1 (nth_partial j (rotproj_inner S w)) := by
        unfold nth_partial
        have h : (1 : WithTop ℕ∞) + 1 ≤ 2 := by decide
        exact hf_smooth.fderiv_right h |>.clm_apply contDiff_const
      have hg_diff : Differentiable ℝ (nth_partial j (rotproj_inner S w)) := by
        have h1ne : (1 : WithTop ℕ∞) ≠ 0 := by decide
        exact hg.differentiable h1ne
      -- Again: nth_partial i (c • g) = c • nth_partial i g
      have hpartial_smul2 : nth_partial i (‖S‖⁻¹ • nth_partial j (rotproj_inner S w)) =
          ‖S‖⁻¹ • nth_partial i (nth_partial j (rotproj_inner S w)) := by
        ext y
        simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
        rw [fderiv_const_smul (c := ‖S‖⁻¹) (hg_diff y)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hpartial_smul2]
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

    -- Get the existence of A with norm bound
    obtain ⟨A, hAnorm, hAeq⟩ := second_partial_inner_rotM_inner S w x i j

    -- Now apply the bound
    rw [hscale, hAeq]
    exact inner_bound_helper A S w w_unit hAnorm

theorem rotation_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_outer_unit S w) := by
  -- First handle the case when ‖S‖ = 0
  by_cases hS : ‖S‖ = 0
  · -- When ‖S‖ = 0, the function is constantly 0
    intro x i j
    have hzero : rotproj_outer_unit S w = 0 := by ext y; simp [rotproj_outer_unit, hS]
    have h1 : nth_partial j (rotproj_outer_unit S w) = 0 := by
      ext y
      simp only [nth_partial, hzero]
      rw [fderiv_zero]
      simp
    simp only [nth_partial, h1]
    rw [fderiv_zero]
    simp
  · -- When ‖S‖ ≠ 0, we have S_nonzero : ‖S‖ > 0
    have S_pos : ‖S‖ > 0 := (norm_nonneg S).lt_of_ne' hS
    intro x i j
    -- The function is rotproj_outer_unit S w = (fun y => ⟪rotM (y 0) (y 1) S, w⟫) / ‖S‖
    -- Its second partial equals (second partial of inner product) / ‖S‖
    -- By second_partial_inner_rotM_outer, the second partial of the inner product is ⟪A S, w⟫
    -- where ‖A‖ ≤ 1, so the full second partial is ⟪A S, w⟫ / ‖S‖
    -- By inner_bound_helper, this has absolute value ≤ 1

    -- First, relate rotproj_outer_unit to the inner product function
    have heq : rotproj_outer_unit S w = fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫ / ‖S‖ := by
      ext y; rfl

    -- The second partial of f/c is (second partial of f) / c
    -- This follows from fderiv (c⁻¹ • f) = c⁻¹ • fderiv f applied twice
    -- Proof: f/c = c⁻¹ • f, and since fderiv commutes with scalar multiplication,
    -- nth_partial i (nth_partial j (f / c)) = nth_partial i (nth_partial j f) / c
    have hscale : nth_partial i (nth_partial j (rotproj_outer_unit S w)) x =
        nth_partial i (nth_partial j (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x / ‖S‖ := by
      -- rotproj_outer_unit S w = f / ‖S‖ where f = ⟪rotM · S, w⟫
      -- nth_partial is ℝ-linear, so nth_partial(f/c) = nth_partial(f)/c
      rw [heq]
      -- The function f/‖S‖ where f = ⟪rotM · S, w⟫ can be written as ‖S‖⁻¹ • f
      let f : E 2 → ℝ := fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫
      have hfun : (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫ / ‖S‖) = ‖S‖⁻¹ • f := by
        ext y; simp [smul_eq_mul, div_eq_inv_mul, f]
      rw [hfun]; clear hfun
      -- f is smooth (polynomial in sin/cos)
      have hf_smooth : ContDiff ℝ ⊤ f := by
        apply ContDiff.inner ℝ _ contDiff_const
        rw [contDiff_piLp]; intro k
        simp only [f, rotM, rotM_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
        fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> fun_prop
      have hf_diff : Differentiable ℝ f := hf_smooth.differentiable WithTop.top_ne_zero
      -- Key lemma: nth_partial j (c • f) = c • nth_partial j f for constant c
      have hpartial_smul : nth_partial j (‖S‖⁻¹ • f) = ‖S‖⁻¹ • nth_partial j f := by
        ext y
        simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
        rw [fderiv_const_smul (c := ‖S‖⁻¹) (hf_diff y)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hpartial_smul]
      -- g = nth_partial j f is also smooth
      have hg : ContDiff ℝ ⊤ (nth_partial j f) := by
        unfold nth_partial
        exact hf_smooth.fderiv_right le_top |>.clm_apply contDiff_const
      have hg_diff : Differentiable ℝ (nth_partial j f) := hg.differentiable WithTop.top_ne_zero
      -- Again: nth_partial i (c • g) = c • nth_partial i g
      have hpartial_smul2 : nth_partial i (‖S‖⁻¹ • nth_partial j f) = ‖S‖⁻¹ • nth_partial i (nth_partial j f) := by
        ext y
        simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
        rw [fderiv_const_smul (c := ‖S‖⁻¹) (hg_diff y)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hpartial_smul2]
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul, f]

    -- Get the existence of A with norm bound
    obtain ⟨A, hAnorm, hAeq⟩ := second_partial_inner_rotM_outer S w x i j

    -- Now apply the bound
    rw [hscale, hAeq]
    exact inner_bound_helper A S w w_unit hAnorm

lemma Differentiable.rotproj_outer (P : ℝ³) (w : ℝ²) : Differentiable ℝ (rotproj_outer P w) :=
  Differentiable.inner ℝ (Differentiable.rotM_outer P) (by fun_prop)

lemma HasFDerivAt.rotproj_outer (pbar : Pose) (P : ℝ³) (w : ℝ²) :
    HasFDerivAt (rotproj_outer P w) (rotproj_outer' pbar P w) pbar.outerParams := by
  have z1 : HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams :=
    HasFDerivAt.rotM_outer pbar P
  have step :
    rotproj_outer' pbar P w = (fderivInnerCLM ℝ
        ((rotM (pbar.outerParams.ofLp 0) (pbar.outerParams.ofLp 1)) P, w)).comp
        ((rotM' pbar P).prod 0) := by
    ext d
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
               ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add, real_inner_comm]
    simp only [rotproj_outer', rotM']
    simp only [LinearMap.coe_toContinuousLinearMap']
    simp only [Module.Basis.constr_apply_fintype]
    simp only [Matrix.toEuclideanLin_apply]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_lhs => rw [show (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.equivFun = (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)) by
      rw [EuclideanSpace.basisFun_toBasis]; exact @PiLp.basisFun_equivFun 2 ℝ (Fin 2) _ _]
    simp only [WithLp.linearEquiv_apply]
    simp only [WithLp.addEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
    conv_rhs => simp only [Matrix.mulVec, Matrix.of_apply]
    simp only [PiLp.inner_apply, Matrix.mulVec, Matrix.of_apply,
               Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    unfold dotProduct
    simp only [Fin.sum_univ_two, smul_eq_mul, Pose.rotM₂θ, Pose.rotM₂φ]
    ring
  rw [step]
  exact HasFDerivAt.inner ℝ z1 (hasFDerivAt_const w pbar.outerParams)

lemma fderiv_rotproj_outer_unit (pbar : Pose) (P : ℝ³) (w : ℝ²) :
    fderiv ℝ (rotproj_outer_unit P w) pbar.outerParams = ‖P‖⁻¹ • (rotproj_outer' pbar P w) := by
  have heq : rotproj_outer_unit P w = ‖P‖⁻¹ • rotproj_outer P w := by
    ext x; simp [rotproj_outer_unit, rotproj_outer, inv_mul_eq_div]
  simp only [heq, HasFDerivAt.rotproj_outer pbar P w |>.const_smul ‖P‖⁻¹ |>.fderiv]

lemma partials_helper3a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    (fderiv ℝ (rotproj_outer_unit P pc.w) pbar.outerParams) (EuclideanSpace.single 0 1) =
    ‖P‖⁻¹ * ⟪pbar.rotM₂θ P, pc.w⟫ := by
  rw [fderiv_rotproj_outer_unit pbar P pc.w]
  simp [rotproj_outer']

lemma partials_helper4a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    (fderiv ℝ (rotproj_outer_unit P pc.w) pbar.outerParams) (EuclideanSpace.single 1 1) =
    ‖P‖⁻¹ * ⟪pbar.rotM₂φ P, pc.w⟫ := by
  rw [fderiv_rotproj_outer_unit pbar P pc.w]
  simp [rotproj_outer']

lemma fderiv_rotproj_inner_unit (pbar : Pose) (S : ℝ³) (w : ℝ²) :
    fderiv ℝ (rotproj_inner_unit S w) pbar.innerParams = ‖S‖⁻¹ • (rotproj_inner' pbar S w) := by
  have heq : rotproj_inner_unit S w = ‖S‖⁻¹ • rotproj_inner S w := by
    ext x; simp [rotproj_inner_unit, rotproj_inner, inv_mul_eq_div]
  simp only [heq, HasFDerivAt.rotproj_inner pbar S w |>.const_smul ‖S‖⁻¹ |>.fderiv]

lemma partials_helper0a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 0 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫  := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper0 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 0 pc.fu pbar.innerParams =
    ⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper0a]
  field_simp

lemma partials_helper1a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 1 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫  := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper1 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 1 pc.fu pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper1a]
  field_simp

lemma partials_helper2a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 2 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫  := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper2 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 2 pc.fu pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper2a]
  field_simp

lemma partials_helper3 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) (hP : ‖P‖ ≠ 0) :
    ‖P‖ * nth_partial 0 (GlobalTheoremPrecondition.fu_outer P pc) pbar.outerParams =
    ⟪pbar.rotM₂θ P, pc.w⟫ := by
  simp only [nth_partial, GlobalTheoremPrecondition.fu_outer, Fin.isValue, partials_helper3a]
  field_simp [hP]

lemma partials_helper4 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) (hP : ‖P‖ ≠ 0) :
    ‖P‖ * nth_partial 1 (GlobalTheoremPrecondition.fu_outer P pc) pbar.outerParams =
    ⟪pbar.rotM₂φ P, pc.w⟫ := by
  simp only [nth_partial, GlobalTheoremPrecondition.fu_outer, Fin.isValue, partials_helper4a]
  field_simp [hP]

lemma partials_helper {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    |⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫| + |⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫| +
      |⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫| = (‖pc.S‖ * ∑ i, |nth_partial i pc.fu pbar.innerParams|) := by
  rw [Finset.mul_sum, Fin.sum_univ_three, ← abs_norm, ← abs_mul, ← abs_mul, ← abs_mul,
    partials_helper0, partials_helper1, partials_helper2]

lemma partials_helper_outer {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) (hP : ‖P‖ ≠ 0) :
    |⟪pbar.rotM₂θ P, pc.w⟫| + |⟪pbar.rotM₂φ P, pc.w⟫| =
    ‖P‖ * ∑ i, |nth_partial i (pc.fu_outer P) pbar.outerParams| := by
  rw [Finset.mul_sum, Fin.sum_univ_two, ← abs_norm, ← abs_mul, ← abs_mul]
  simp only [Fin.isValue]
  rw [partials_helper3 pc P hP, partials_helper4 pc P hP]

theorem fu_times_norm_S_eq_f {pbar p : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.fu p.innerParams * ‖pc.S‖ = pc.f p.innerParams := by
  have := pc.norm_S_ne_zero
  simp only [GlobalTheoremPrecondition.fu, GlobalTheoremPrecondition.f, rotproj_inner_unit, rotproj_inner]
  field_simp

lemma rotproj_helper {pbar p : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    |pc.fu pbar.innerParams - pc.fu p.innerParams| * ‖pc.S‖ = |⟪pbar.inner pc.S, pc.w⟫ - pc.Sval p| := by
  rw [← f_pose_eq_sval, ← f_pose_eq_inner]
  repeat rw [← fu_times_norm_S_eq_f]
  rw [← sub_mul]
  simp

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_ii (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    G pbar ε pc.S pc.w ≤ pc.Sval p := by
  have S_norm_pos : 0 < ‖pc.S‖ := pc.norm_S_gt_zero
  have S_norm_le_one : ‖pc.S‖ ≤ 1 := pc.norm_S_le_one
  have hz := bounded_partials_control_difference
    pc.fu (rotation_partials_exist S_norm_pos)
    pbar.innerParams p.innerParams ε hε
    (closed_ball_imp_inner_params_near p_near_pbar)
    (rotation_partials_bounded pc.S pc.w_unit)
  simp only [G]
  refine sub_le_of_abs_sub_le_right ?_
  have hzs := mul_le_mul_of_nonneg_right hz (ha := le_of_lt S_norm_pos)
  rw [← rotproj_helper pc, partials_helper pc]
  norm_num at hzs
  ring_nf at hzs ⊢
  nth_grw 3 [S_norm_le_one] at hzs
  simp_all only [one_mul]

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_iv (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    maxOuter p poly pc.w ≤ maxH pbar poly ε pc.w := by
  -- First of all, we can relate these two maximums by relating
  -- their components.
  suffices h : ∀ vert ∈ poly.vertices,
      ⟪pc.w, p.outer vert⟫ ≤ H pbar ε pc.w vert by
    simp only [maxH, maxOuter, imgOuter, Finset.max'_le_iff, Finset.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    simp only [Finset.max', Finset.sup'_image,
      Finset.le_sup'_iff]
    exact fun a ha => Exists.intro a ⟨ha, h a ha⟩
  -- Now we're just considering a single polyhedron vertex P
  intro P hP
  have P_norm_pos : 0 < ‖P‖ := poly.nontriv P hP
  have P_norm_le_one : ‖P‖ ≤ 1 := poly.vertex_radius_le_one P hP

  have hz := bounded_partials_control_difference
    (pc.fu_outer P) (rotation_partials_exist_outer P_norm_pos)
    pbar.outerParams p.outerParams ε hε
    (closed_ball_imp_outer_params_near p_near_pbar)
    (rotation_partials_bounded_outer P pc.w_unit)
  simp_all only [H]
  rw [abs_sub_comm] at hz
  replace hz := sub_le_of_abs_sub_le_right hz
  rw [tsub_le_iff_right] at hz
  replace hz := mul_le_mul_of_nonneg_right hz (ha := le_of_lt P_norm_pos)
  rw [add_mul] at hz
  rw [pc.fu_pose_eq_outer P, pc.fu_pose_eq_outer P] at hz
  rw [partials_helper_outer pc P (ne_of_gt P_norm_pos)]
  rw [show pbar.rotM₂ P = pbar.outer P by rw [Pose.outer_eq_M]]
  conv => enter [2, 1, 1]; rw [real_inner_comm]
  ring_nf at hz ⊢
  nth_grw 2 [P_norm_le_one] at hz
  simp only [mul_one] at hz
  exact hz

/--
Here we run through the "sequence of inequalities [which yield] the desired contradiction"
-/
theorem global_theorem_gt_reasoning (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
     maxInner p poly pc.w > maxOuter p poly pc.w
    := by
  have sval_in_img_inner : pc.Sval p ∈ imgInner p poly.vertices pc.w := by
    simp only [Finset.mem_image, imgInner, GlobalTheoremPrecondition.Sval]
    use pc.S, pc.S_in_poly

  calc
    maxInner p poly pc.w
    _ ≥ pc.Sval p := Finset.le_max' (H2 := sval_in_img_inner)
    _ ≥ G pbar ε pc.S pc.w := global_theorem_inequality_ii pbar p ε hε p_near_pbar poly pc
    _ > maxH pbar poly ε pc.w := pc.exceeds
    _ ≥ maxOuter p poly pc.w := global_theorem_inequality_iv pbar p ε hε p_near_pbar poly pc

/--
The Global Theorem, [SY25] Theorem 17
-/
theorem global_theorem (pbar : Pose) (ε : ℝ) (hε : ε > 0)
    (poly : GoodPoly)
    (_poly_pointsym : PointSym poly.hull)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ¬ ∃ p ∈ pbar.closed_ball ε, RupertPose p poly.hull := by
  rintro ⟨p, p_near_pbar, p_is_rupert⟩
  have hgt := global_theorem_gt_reasoning pbar p ε hε p_near_pbar poly pc
  have hle := global_theorem_le_reasoning p poly p_is_rupert pc.w
  exact lt_irrefl _ (lt_of_lt_of_le hgt hle)

/--
The Global Theorem specialized to the noperthedron.
-/
theorem global_theorem_nopert (pbar : Pose) (ε : ℝ) (hε : ε > 0)
    (pc : GlobalTheoremPrecondition Nopert.poly pbar ε) :
    ¬ ∃ p ∈ pbar.closed_ball ε, RupertPose p nopert.hull :=
  global_theorem pbar ε hε Nopert.poly
      nopert_point_symmetric pc

end GlobalTheorem
