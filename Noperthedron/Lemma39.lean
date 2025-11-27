import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RationalApprox

noncomputable section

theorem norm_le_delta_sqrt_dims {m n : ℕ} {δ : ℝ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hδ : 0 < δ) (hle : ∀ i j, |A i j| ≤ δ) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ δ * √(m * n) := by
  simp only [ContinuousLinearMap.norm_def, LinearMap.coe_toContinuousLinearMap']
  refine csInf_le (by use 0; intro b hb; exact hb.1) ?_
  refine ⟨by positivity, ?_⟩
  intro v
  suffices h : ‖(Matrix.toEuclideanLin A) v‖^2 ≤ (δ * √(↑m * ↑n) * ‖v‖)^2 from
    (sq_le_sq₀ (by positivity) (by positivity)).mp h
  simp only [PiLp.norm_sq_eq_of_L2, Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply,
    Real.norm_eq_abs, sq_abs, Nat.cast_nonneg, Real.sqrt_mul, mul_pow, Real.sq_sqrt]
  ring_nf
  sorry
