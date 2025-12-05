import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RationalApprox

noncomputable section

theorem sum_mul_sq_le_sum_mul_abs_sq {n : ℕ} (v w : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hle : ∀ j, |w j| ≤ δ) :
    (∑ j, w j * v j)^2 ≤ (∑ j, δ * |v j|)^2 := by
  calc (∑ j, w j * v j)^2
    _ ≤ (|(∑ j, w j * v j)|)^2 := by rw [sq_abs]
    _ ≤ ((∑ j, |w j * v j|))^2 := by
        refine (sq_le_sq₀ (by positivity) (by positivity)).mpr ?_
        exact Finset.abs_sum_le_sum_abs (fun i ↦ w i * v i) Finset.univ
    _ = ((∑ j, |w j| * |v j|))^2 := by simp
    _ ≤ (∑ j, δ * |v j|)^2 := by
        refine (sq_le_sq₀ (by positivity) (by positivity)).mpr ?_
        apply Finset.sum_le_sum
        intro i hi
        grw [hle i]

theorem sum_abs_sq_le_sum_abs_sq_mul {n : ℕ} (v : Fin n → ℝ) :
    (∑ j, |v j|) ^ 2 ≤ (∑ j, |v j| ^ 2) * n := by
  have h : (∑ j, |v j| * 1)^2  ≤ (∑ j, |v j| ^ 2) * (∑ _ : Fin n, 1 ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |v j|) (fun _ => 1)
  simpa using h

theorem norm_le_delta_sqrt_dims {m n : ℕ} {δ : ℝ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hδ : 0 < δ) (hle : ∀ i j, |A i j| ≤ δ) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ δ * √(m * n) := by
  simp only [ContinuousLinearMap.norm_def, LinearMap.coe_toContinuousLinearMap']
  refine csInf_le (by use 0; intro b hb; exact hb.1) ?_
  refine ⟨by positivity, ?_⟩
  intro v
  suffices h : ‖(Matrix.toEuclideanLin A) v‖^2 ≤ (δ * √(m * n) * ‖v‖)^2 from
    (sq_le_sq₀ (by positivity) (by positivity)).mp h
  simp only [Nat.cast_nonneg, Real.sqrt_mul, mul_pow, Real.sq_sqrt]
  ring_nf

  calc ‖A.toEuclideanLin v‖^2
    _ = ∑ i, A.mulVec v.ofLp i ^ 2 := by simp [PiLp.norm_sq_eq_of_L2]
    _ = ∑ i, (∑ j, A i j * v j) ^ 2 := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ i : Fin m, (∑ j, δ * |v j|) ^ 2 :=
        Finset.sum_le_sum (fun i _ => sum_mul_sq_le_sum_mul_abs_sq v.ofLp (A i) δ hδ (hle i))
    _ = m * (∑ j, δ * |v j|) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = m * (δ * (∑ j, |v j|)) ^ 2 := by rw [← Finset.mul_sum]
    _ = m * δ^2 * (∑ j, |v j|) ^ 2 := by rw [mul_pow]; ring_nf
    _ ≤ m * δ^2 * (∑ j, |v j| ^ 2) * n := by grw [sum_abs_sq_le_sum_abs_sq_mul v]; ring_nf; simp only [le_refl]
    _ = m * δ^2 * (∑ j, (v j) ^ 2) * n := by conv in (∑ j, _) => rhs; intro j; rw [sq_abs]
    _ = δ ^ 2 * m * n * ‖v‖^2 := by simp [PiLp.norm_sq_eq_of_L2]; ring_nf
