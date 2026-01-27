import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Noperthedron.Basic

lemma hasDerivAt_pi2 (f g : ℝ → ℝ) (f' g' t : ℝ)
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun x ↦ ![f x, g x]) (![f', g']) t := by
  simp [hasDerivAt_pi, hf, hg]

lemma hasDerivAt_clm_pi2 (f g : ℝ → ℝ) (f' g' t : ℝ)
    {F : Type} [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F]
    (h : (Fin 2 → ℝ) →L[ℝ] F)
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun x ↦ h (![f x, g x])) (h (![f', g'])) t := by
  simpa using HasDerivAt.clm_apply (hasDerivAt_const t h) (hasDerivAt_pi2 f g f' g' t hf hg)

lemma hasDerivAt_lp2 {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun x ↦ !₂[f x, g x]) (!₂[f', g']) t := by
  let lpmap := WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ) |>.symm.toContinuousLinearMap
  exact (hasDerivAt_clm_pi2 f g f' g' t lpmap) hf hg

theorem HasDerivAt_rotR_mat (α : ℝ) (v : ℝ²) :
    HasDerivAt (fun α ↦ !₂[Real.cos α * v 0 + -(Real.sin α * v 1), Real.sin α * v 0 + Real.cos α * v 1])
    !₂[-(Real.sin α * v 0) + -(Real.cos α * v 1), Real.cos α * v 0 + -(Real.sin α * v 1)] α := by
  refine hasDerivAt_lp2 ?_ ?_
  · let f (x : ℝ) := Real.cos x * v 0 + -(Real.sin x * v 1)
    rw [show -(Real.sin α * v 0) + -(Real.cos α * v 1) = deriv f α by simp [f]]
    refine DifferentiableAt.hasDerivAt ?_; simp
  · let f (x : ℝ) := Real.sin x * v 0 + Real.cos x * v 1
    rw [show (Real.cos α * v 0) + -(Real.sin α * v 1) = deriv f α by simp [f]]
    refine DifferentiableAt.hasDerivAt ?_; simp

theorem HasDerivAt_rotR (α : ℝ) (v : ℝ²) :
    HasDerivAt (rotR · v) (rotR' α v) α := by
  simpa [Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail, rotR] using HasDerivAt_rotR_mat α v

/-!
## Derivatives of rotation matrices rotM, rotMθ, rotMφ w.r.t. angles

These are needed for computing first and second partial derivatives of rotproj functions.
Each proves HasDerivAt for the rotation matrix (or its derivative) applied to a fixed vector S.
-/

/-- Derivative of rotM w.r.t. θ gives rotMθ -/
lemma hasDerivAt_rotM_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotM θ' φ S) (rotMθ θ φ S) θ := by
  have h_f : (fun θ' => rotM θ' φ S) = (fun θ' => !₂[-Real.sin θ' * S 0 + Real.cos θ' * S 1,
      -Real.cos θ' * Real.cos φ * S 0 - Real.sin θ' * Real.cos φ * S 1 + Real.sin φ * S 2]) := by
    ext θ' i; fin_cases i <;> (simp [rotM, rotM_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMθ θ φ S = !₂[-Real.cos θ * S 0 - Real.sin θ * S 1,
      Real.sin θ * Real.cos φ * S 0 - Real.cos θ * Real.cos φ * S 1] := by
    ext i; fin_cases i <;> (simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · have h : deriv (fun x => -Real.sin x * S 0 + Real.cos x * S 1) θ = -Real.cos θ * S 0 - Real.sin θ * S 1 := by simp; ring
    rw [← h]; exact DifferentiableAt.hasDerivAt (by fun_prop)
  · have h1 : HasDerivAt (fun x => -Real.cos x * Real.cos φ * S 0) (Real.sin θ * Real.cos φ * S 0) θ := by
      have := (Real.hasDerivAt_cos θ).neg.mul_const (Real.cos φ * S 0)
      simp only [neg_neg, mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin x * Real.cos φ * S 1) (Real.cos θ * Real.cos φ * S 1) θ := by
      have := (Real.hasDerivAt_sin θ).mul_const (Real.cos φ * S 1)
      simp only [mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun _ : ℝ => Real.sin φ * S 2) 0 θ := hasDerivAt_const _ _
    convert (h1.sub h2).add h3 using 1; ring

/-- Derivative of rotM w.r.t. φ gives rotMφ -/
lemma hasDerivAt_rotM_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotM θ φ' S) (rotMφ θ φ S) φ := by
  have h_f : (fun φ' => rotM θ φ' S) = (fun φ' => !₂[-Real.sin θ * S 0 + Real.cos θ * S 1,
      -Real.cos θ * Real.cos φ' * S 0 - Real.sin θ * Real.cos φ' * S 1 + Real.sin φ' * S 2]) := by
    ext φ' i; fin_cases i <;> (simp [rotM, rotM_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMφ θ φ S = !₂[(0 : ℝ),
      Real.cos θ * Real.sin φ * S 0 + Real.sin θ * Real.sin φ * S 1 + Real.cos φ * S 2] := by
    ext i; fin_cases i <;> (simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => -Real.cos θ * Real.cos x * S 0) (Real.cos θ * Real.sin φ * S 0) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (-Real.cos θ)).mul_const (S 0)
      simp only [neg_mul, mul_neg, neg_neg, mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin θ * Real.cos x * S 1) (-Real.sin θ * Real.sin φ * S 1) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (Real.sin θ)).mul_const (S 1)
      simp only [neg_mul, mul_neg, mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun x => Real.sin x * S 2) (Real.cos φ * S 2) φ := (Real.hasDerivAt_sin φ).mul_const (S 2)
    convert (h1.sub h2).add h3 using 1; ring

/-- Derivative of rotMθ w.r.t. θ gives rotMθθ -/
lemma hasDerivAt_rotMθ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθ θ' φ S) (rotMθθ θ φ S) θ := by
  have h_f : (fun θ' => rotMθ θ' φ S) = (fun θ' => !₂[-Real.cos θ' * S 0 - Real.sin θ' * S 1,
      Real.sin θ' * Real.cos φ * S 0 - Real.cos θ' * Real.cos φ * S 1]) := by
    ext θ' i; fin_cases i <;> (simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMθθ θ φ S = !₂[Real.sin θ * S 0 - Real.cos θ * S 1,
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1] := by
    ext i; fin_cases i <;> (simp [rotMθθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · have h : deriv (fun x => -Real.cos x * S 0 - Real.sin x * S 1) θ = Real.sin θ * S 0 - Real.cos θ * S 1 := by simp
    rw [← h]; exact DifferentiableAt.hasDerivAt (by fun_prop)
  · have h1 : HasDerivAt (fun x => Real.sin x * Real.cos φ * S 0) (Real.cos θ * Real.cos φ * S 0) θ := by
      have := (Real.hasDerivAt_sin θ).mul_const (Real.cos φ * S 0); simp only [mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.cos x * Real.cos φ * S 1) (-Real.sin θ * Real.cos φ * S 1) θ := by
      have := (Real.hasDerivAt_cos θ).mul_const (Real.cos φ * S 1); simp only [mul_assoc, neg_mul] at this ⊢; exact this
    convert h1.sub h2 using 1; ring

/-- Derivative of rotMθ w.r.t. φ gives rotMθφ -/
lemma hasDerivAt_rotMθ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθ θ φ' S) (rotMθφ θ φ S) φ := by
  have h_f : (fun φ' => rotMθ θ φ' S) = (fun φ' => !₂[-Real.cos θ * S 0 - Real.sin θ * S 1,
      Real.sin θ * Real.cos φ' * S 0 - Real.cos θ * Real.cos φ' * S 1]) := by
    ext φ' i; fin_cases i <;> (simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
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

/-- Derivative of rotMφ w.r.t. θ gives rotMθφ -/
lemma hasDerivAt_rotMφ_θ (θ φ : ℝ) (S : ℝ³) :
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

/-- Derivative of rotMφ w.r.t. φ gives rotMφφ -/
lemma hasDerivAt_rotMφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMφ θ φ' S) (rotMφφ θ φ S) φ := by
  have h_f : (fun φ' => rotMφ θ φ' S) = (fun φ' => !₂[(0 : ℝ),
      Real.cos θ * Real.sin φ' * S 0 + Real.sin θ * Real.sin φ' * S 1 + Real.cos φ' * S 2]) := by
    ext φ' i; fin_cases i <;> (simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMφφ θ φ S = !₂[(0 : ℝ),
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1 - Real.sin φ * S 2] := by
    ext i; fin_cases i <;> (simp [rotMφφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
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
