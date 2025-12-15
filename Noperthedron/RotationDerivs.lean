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
  simp [Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail, HasDerivAt_rotR_mat α v]
