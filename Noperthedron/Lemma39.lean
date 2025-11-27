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
  simp only [Nat.cast_nonneg, Real.sqrt_mul, mul_pow, Real.sq_sqrt]
  ring_nf

  calc ‖A.toEuclideanLin v‖^2
    _ = ∑ i, A.mulVec v.ofLp i ^ 2 := by simp [PiLp.norm_sq_eq_of_L2]
    _ = ∑ i, (∑ j, A i j * v j) ^ 2 := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ i : Fin m, (∑ j, δ * |v j|) ^ 2 := by sorry
    _ = m * (∑ j, δ * |v j|) ^ 2 := by sorry
    _ = m * (δ * ∑ j, |v j|) ^ 2 := by sorry
    _ = m * δ^2 * (∑ j, |v j|) ^ 2 := by sorry
    _ ≤ m * δ^2 * (∑ j : Fin n, ‖v‖) ^ 2 := by sorry
    _ ≤  δ ^ 2 * m * n * ‖v‖^2 := by  simp [PiLp.norm_sq_eq_of_L2]; sorry
