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

/-- Derivative of a * sin t + b * cos t is a * cos t - b * sin t -/
lemma hasDerivAt_sin_cos_lincomb (a b t : ℝ) :
    HasDerivAt (fun x => a * Real.sin x + b * Real.cos x) (a * Real.cos t - b * Real.sin t) t := by
  convert (Real.hasDerivAt_sin t).const_mul a |>.add ((Real.hasDerivAt_cos t).const_mul b) using 1
  ring

/-- Derivative of a * cos t + b * sin t is -a * sin t + b * cos t -/
lemma hasDerivAt_cos_sin_lincomb (a b t : ℝ) :
    HasDerivAt (fun x => a * Real.cos x + b * Real.sin x) (-a * Real.sin t + b * Real.cos t) t := by
  convert (Real.hasDerivAt_cos t).const_mul a |>.add ((Real.hasDerivAt_sin t).const_mul b) using 1
  ring

theorem HasDerivAt_rotR_mat (α : ℝ) (v : ℝ²) :
    HasDerivAt (fun α ↦ !₂[Real.cos α * v 0 + -(Real.sin α * v 1), Real.sin α * v 0 + Real.cos α * v 1])
    !₂[-(Real.sin α * v 0) + -(Real.cos α * v 1), Real.cos α * v 0 + -(Real.sin α * v 1)] α := by
  refine hasDerivAt_lp2 ?_ ?_
  · convert hasDerivAt_cos_sin_lincomb (v 0) (-v 1) α using 1
    · funext; ring
    · ring
  · convert hasDerivAt_sin_cos_lincomb (v 0) (v 1) α using 1
    · funext; ring
    · ring

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
    ext i; fin_cases i <;> (simp [rotMθ, rotMθ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · convert hasDerivAt_sin_cos_lincomb (-S 0) (S 1) θ using 1
    · funext; ring
    · ring
  · convert (hasDerivAt_cos_sin_lincomb (-Real.cos φ * S 0) (-Real.cos φ * S 1) θ).add
        (hasDerivAt_const θ (Real.sin φ * S 2)) using 1
    · funext; simp only [Pi.add_apply]; ring
    · ring

/-- Derivative of rotM w.r.t. φ gives rotMφ -/
lemma hasDerivAt_rotM_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotM θ φ' S) (rotMφ θ φ S) φ := by
  have h_f : (fun φ' => rotM θ φ' S) = (fun φ' => !₂[-Real.sin θ * S 0 + Real.cos θ * S 1,
      -Real.cos θ * Real.cos φ' * S 0 - Real.sin θ * Real.cos φ' * S 1 + Real.sin φ' * S 2]) := by
    ext φ' i; fin_cases i <;> (simp [rotM, rotM_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMφ θ φ S = !₂[(0 : ℝ),
      Real.cos θ * Real.sin φ * S 0 + Real.sin θ * Real.sin φ * S 1 + Real.cos φ * S 2] := by
    ext i; fin_cases i <;> (simp [rotMφ, rotMφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · convert hasDerivAt_cos_sin_lincomb (-Real.cos θ * S 0 - Real.sin θ * S 1) (S 2) φ using 1
    · funext; ring
    · ring

/-- Derivative of rotMθ w.r.t. θ gives rotMθθ -/
lemma hasDerivAt_rotMθ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθ θ' φ S) (rotMθθ θ φ S) θ := by
  have h_f : (fun θ' => rotMθ θ' φ S) = (fun θ' => !₂[-Real.cos θ' * S 0 - Real.sin θ' * S 1,
      Real.sin θ' * Real.cos φ * S 0 - Real.cos θ' * Real.cos φ * S 1]) := by
    ext θ' i; fin_cases i <;> (simp [rotMθ, rotMθ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMθθ θ φ S = !₂[Real.sin θ * S 0 - Real.cos θ * S 1,
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1] := by
    ext i; fin_cases i <;> (simp [rotMθθ, rotMθθ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · convert hasDerivAt_cos_sin_lincomb (-S 0) (-S 1) θ using 1
    · funext; ring
    · ring
  · convert hasDerivAt_sin_cos_lincomb (Real.cos φ * S 0) (-Real.cos φ * S 1) θ using 1
    · funext; ring
    · ring

/-- Derivative of rotMθ w.r.t. φ gives rotMθφ -/
lemma hasDerivAt_rotMθ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθ θ φ' S) (rotMθφ θ φ S) φ := by
  have h_f : (fun φ' => rotMθ θ φ' S) = (fun φ' => !₂[-Real.cos θ * S 0 - Real.sin θ * S 1,
      Real.sin θ * Real.cos φ' * S 0 - Real.cos θ * Real.cos φ' * S 1]) := by
    ext φ' i; fin_cases i <;> (simp [rotMθ, rotMθ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMθφ θ φ S = !₂[(0 : ℝ), -Real.sin θ * Real.sin φ * S 0 + Real.cos θ * Real.sin φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθφ, rotMθφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · convert hasDerivAt_cos_sin_lincomb (Real.sin θ * S 0 - Real.cos θ * S 1) 0 φ using 1
    · funext; ring
    · ring

/-- Derivative of rotMφ w.r.t. θ gives rotMθφ -/
lemma hasDerivAt_rotMφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMφ θ' φ S) (rotMθφ θ φ S) θ := by
  have h_f : (fun θ' => rotMφ θ' φ S) = (fun θ' => !₂[(0 : ℝ),
      Real.cos θ' * Real.sin φ * S 0 + Real.sin θ' * Real.sin φ * S 1 + Real.cos φ * S 2]) := by
    ext θ' i; fin_cases i <;> (simp [rotMφ, rotMφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMθφ θ φ S = !₂[(0 : ℝ), -Real.sin θ * Real.sin φ * S 0 + Real.cos θ * Real.sin φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθφ, rotMθφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · convert (hasDerivAt_cos_sin_lincomb (Real.sin φ * S 0) (Real.sin φ * S 1) θ).add
        (hasDerivAt_const θ (Real.cos φ * S 2)) using 1
    · funext; simp only [Pi.add_apply]; ring
    · ring

/-- Derivative of rotMφ w.r.t. φ gives rotMφφ -/
lemma hasDerivAt_rotMφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMφ θ φ' S) (rotMφφ θ φ S) φ := by
  have h_f : (fun φ' => rotMφ θ φ' S) = (fun φ' => !₂[(0 : ℝ),
      Real.cos θ * Real.sin φ' * S 0 + Real.sin θ * Real.sin φ' * S 1 + Real.cos φ' * S 2]) := by
    ext φ' i; fin_cases i <;> (simp [rotMφ, rotMφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMφφ θ φ S = !₂[(0 : ℝ),
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1 - Real.sin φ * S 2] := by
    ext i; fin_cases i <;> (simp [rotMφφ, rotMφφ_mat, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · convert hasDerivAt_sin_cos_lincomb (Real.cos θ * S 0 + Real.sin θ * S 1) (S 2) φ using 1
    · funext; ring
    · ring
