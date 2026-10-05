module

public import Noperthedron.PentagonalHexecontahedron.BernsteinBound

@[expose] public section

/-!
# The tensor Bernstein bound

A polynomial in n variables with degree at most d_i in variable i, given on
[0, 1]ⁿ by its coefficients a_f (f ≤ d componentwise), equals
Σ_k b_k Π_i B_{d_i, k_i}(y_i) with the tensor Bernstein coefficients
b_k = Σ_{f ≤ k} a_f Π_i C(k_i, f_i)/C(d_i, f_i); the basis products are
nonnegative and sum to 1, so the value is at least min_k b_k
(`tensor_bernstein_lower`).
-/

namespace Noperthedron.PentagonalHexecontahedron.Bernstein

open Finset

variable {n : ℕ}

/-- Multi-indices f with f_i ≤ d_i. -/
def box (d : Fin n → ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun i => range (d i + 1)

/-- The univariate weight C(k, f)/C(d, f). -/
noncomputable def weight (d k f : ℕ) : ℝ := (k.choose f : ℝ) / (d.choose f : ℝ)

/-- y^f = Σ_k weight(d, k, f) B_{d,k}(y) for f ≤ d. -/
theorem pow_eq_sum_weight_basis (d f : ℕ) (hf : f ≤ d) (y : ℝ) :
    y ^ f = ∑ k ∈ range (d + 1), weight d k f * basis d k y := by
  have h := sum_choose_basis d f hf y
  have hcd : (d.choose f : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hf).ne'
  unfold weight
  calc y ^ f = ((d.choose f : ℝ) * y ^ f) / (d.choose f : ℝ) := by field_simp
    _ = _ := by
      rw [← h, sum_div]
      apply sum_congr rfl
      intro k _
      ring

/-- The tensor Bernstein coefficient. -/
noncomputable def tensorCoeff (d : Fin n → ℕ) (a : (Fin n → ℕ) → ℝ) (k : Fin n → ℕ) : ℝ :=
  ∑ f ∈ box d, a f * ∏ i, weight (d i) (k i) (f i)

noncomputable def tensorBasis (d : Fin n → ℕ) (k : Fin n → ℕ) (y : Fin n → ℝ) : ℝ :=
  ∏ i, basis (d i) (k i) (y i)

theorem eval_eq_tensor (d : Fin n → ℕ) (a : (Fin n → ℕ) → ℝ) (y : Fin n → ℝ) :
    ∑ f ∈ box d, a f * ∏ i, y i ^ f i =
      ∑ k ∈ box d, tensorCoeff d a k * tensorBasis d k y := by
  have hmono : ∀ f ∈ box d, ∏ i, y i ^ f i =
      ∑ k ∈ box d, (∏ i, weight (d i) (k i) (f i)) * tensorBasis d k y := by
    intro f hf
    have hfi : ∀ i, f i ≤ d i := by
      intro i
      have := (Fintype.mem_piFinset.mp hf) i
      rw [mem_range] at this
      omega
    calc ∏ i, y i ^ f i = ∏ i, ∑ k ∈ range (d i + 1), weight (d i) k (f i) * basis (d i) k (y i) :=
          prod_congr rfl fun i _ => pow_eq_sum_weight_basis (d i) (f i) (hfi i) (y i)
      _ = ∑ k ∈ Fintype.piFinset (fun i => range (d i + 1)),
            ∏ i, weight (d i) (k i) (f i) * basis (d i) (k i) (y i) := prod_univ_sum _ _
      _ = _ := by
          apply sum_congr rfl
          intro k _
          rw [tensorBasis, ← prod_mul_distrib]
  rw [sum_congr rfl fun f hf => by rw [hmono f hf]]
  simp only [mul_sum, tensorCoeff, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro f _
  ring

theorem tensorBasis_nonneg (d k : Fin n → ℕ) {y : Fin n → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    0 ≤ tensorBasis d k y :=
  prod_nonneg fun i _ => basis_nonneg (d i) (k i) (hy i).1 (hy i).2

theorem sum_tensorBasis (d : Fin n → ℕ) (y : Fin n → ℝ) :
    ∑ k ∈ box d, tensorBasis d k y = 1 := by
  unfold box tensorBasis
  rw [← prod_univ_sum (fun i => range (d i + 1)) (fun i k => basis (d i) k (y i))]
  exact prod_eq_one fun i _ => sum_basis (d i) (y i)

/-- The tensor Bernstein lower bound on [0, 1]ⁿ. -/
theorem tensor_bernstein_lower (d : Fin n → ℕ) (a : (Fin n → ℕ) → ℝ) (L : ℝ)
    (hL : ∀ k ∈ box d, L ≤ tensorCoeff d a k) {y : Fin n → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    L ≤ ∑ f ∈ box d, a f * ∏ i, y i ^ f i := by
  rw [eval_eq_tensor]
  calc L = ∑ k ∈ box d, L * tensorBasis d k y := by rw [← mul_sum, sum_tensorBasis, mul_one]
    _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hL k hk) (tensorBasis_nonneg d k hy)

end Noperthedron.PentagonalHexecontahedron.Bernstein
