module

public import Mathlib

@[expose] public section

/-!
# The univariate Bernstein bound

For a polynomial Σ_{j ≤ d} a_j y^j and y ∈ [0, 1], the value is a convex
combination of the Bernstein coefficients b_k = Σ_{j ≤ k} C(k, j)/C(d, j) a_j
(with weights C(d, k) y^k (1 − y)^{d − k}), so it is at least min_k b_k
(`bernstein_lower`). Applied one variable at a time this gives the tensor
Bernstein bound used by the DH's tie-tube and cap checkers.
-/

namespace Noperthedron.PentagonalHexecontahedron.Bernstein

open Finset

/-- The Bernstein coefficient b_k of Σ_{j ≤ d} a_j y^j. -/
noncomputable def coeff (d : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), ((k.choose j : ℝ) / (d.choose j : ℝ)) * a j

/-- The Bernstein basis polynomial. -/
noncomputable def basis (d k : ℕ) (y : ℝ) : ℝ := (d.choose k : ℝ) * y ^ k * (1 - y) ^ (d - k)

theorem basis_nonneg (d k : ℕ) {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ basis d k y := by
  unfold basis
  have : 0 ≤ 1 - y := by linarith
  positivity

theorem sum_basis (d : ℕ) (y : ℝ) : ∑ k ∈ range (d + 1), basis d k y = 1 := by
  have h := (add_pow y (1 - y) d).symm
  simp only [add_sub_cancel, one_pow] at h
  rw [← h]
  apply sum_congr rfl
  intro k _
  unfold basis
  ring

/-- Σ_{k = j}^{d} C(k, j) C(d, k) y^k (1 − y)^{d − k} = C(d, j) y^j. -/
theorem sum_choose_basis (d j : ℕ) (hj : j ≤ d) (y : ℝ) :
    ∑ k ∈ range (d + 1), (k.choose j : ℝ) * basis d k y = (d.choose j : ℝ) * y ^ j := by
  -- Terms with k < j vanish; reindex k = j + m.
  have hsplit : ∑ k ∈ range (d + 1), (k.choose j : ℝ) * basis d k y =
      ∑ m ∈ range (d - j + 1), ((j + m).choose j : ℝ) * basis d (j + m) y := by
    have hd : d + 1 = j + (d - j + 1) := by omega
    rw [hd, sum_range_add]
    have hz : ∑ k ∈ range j, (k.choose j : ℝ) * basis d k y = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [mem_range] at hk
      simp [Nat.choose_eq_zero_of_lt hk]
    rw [hz, zero_add]
  rw [hsplit]
  have hterm : ∀ m ∈ range (d - j + 1), ((j + m).choose j : ℝ) * basis d (j + m) y =
      (d.choose j : ℝ) * y ^ j * (((d - j).choose m : ℝ) * y ^ m * (1 - y) ^ (d - j - m)) := by
    intro m hm
    rw [mem_range] at hm
    unfold basis
    have hc : ((j + m).choose j : ℝ) * (d.choose (j + m) : ℝ) = (d.choose j : ℝ) * ((d - j).choose m : ℝ) := by
      have := Nat.choose_mul (n := d) (k := j + m) (s := j) (by omega)
      rw [show j + m - j = m by omega] at this
      exact_mod_cast (by rw [mul_comm]; exact this)
    have he : d - (j + m) = d - j - m := by omega
    rw [he, pow_add]
    calc ((j + m).choose j : ℝ) * ((d.choose (j + m) : ℝ) * (y ^ j * y ^ m) * (1 - y) ^ (d - j - m))
        = (((j + m).choose j : ℝ) * (d.choose (j + m) : ℝ)) * (y ^ j * y ^ m) * (1 - y) ^ (d - j - m) := by ring
      _ = _ := by rw [hc]; ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hb := (add_pow y (1 - y) (d - j)).symm
  simp only [add_sub_cancel, one_pow] at hb
  have hsum : ∑ m ∈ range (d - j + 1), ((d - j).choose m : ℝ) * y ^ m * (1 - y) ^ (d - j - m) = 1 := by
    calc _ = ∑ m ∈ range (d - j + 1), y ^ m * (1 - y) ^ (d - j - m) * ((d - j).choose m : ℝ) :=
          sum_congr rfl fun m _ => by ring
      _ = 1 := hb
  rw [hsum, mul_one]

/-- The Bernstein representation. -/
theorem eval_eq_sum_coeff_basis (d : ℕ) (a : ℕ → ℝ) (y : ℝ) :
    ∑ j ∈ range (d + 1), a j * y ^ j = ∑ k ∈ range (d + 1), coeff d a k * basis d k y := by
  unfold coeff
  simp only [sum_mul]
  -- Σ_k Σ_{j ≤ k} c(k,j) a_j B_k = Σ_j a_j / C(d,j) Σ_{k} C(k,j) B_k (terms with j > k vanish).
  have hext : ∀ k ∈ range (d + 1), ∑ j ∈ range (k + 1), (k.choose j : ℝ) / (d.choose j : ℝ) * a j * basis d k y =
      ∑ j ∈ range (d + 1), (k.choose j : ℝ) / (d.choose j : ℝ) * a j * basis d k y := by
    intro k hk
    rw [mem_range] at hk
    have hle : k + 1 ≤ d + 1 := by omega
    rw [← sum_range_add_sum_Ico _ hle]
    have hz : ∑ j ∈ Ico (k + 1) (d + 1), (k.choose j : ℝ) / (d.choose j : ℝ) * a j * basis d k y = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [mem_Ico] at hj
      simp [Nat.choose_eq_zero_of_lt (show k < j by omega)]
    rw [hz, add_zero]
  rw [sum_congr rfl hext, sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have hcd : (d.choose j : ℝ) ≠ 0 := by
    have := Nat.choose_pos (show j ≤ d by omega)
    exact_mod_cast this.ne'
  have h := sum_choose_basis d j (by omega) y
  calc a j * y ^ j = a j / (d.choose j : ℝ) * ((d.choose j : ℝ) * y ^ j) := by field_simp
    _ = a j / (d.choose j : ℝ) * ∑ k ∈ range (d + 1), (k.choose j : ℝ) * basis d k y := by rw [h]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring

/-- The Bernstein lower bound on [0, 1]. -/
theorem bernstein_lower (d : ℕ) (a : ℕ → ℝ) (L : ℝ) (hL : ∀ k ≤ d, L ≤ coeff d a k)
    {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    L ≤ ∑ j ∈ range (d + 1), a j * y ^ j := by
  rw [eval_eq_sum_coeff_basis]
  calc L = ∑ k ∈ range (d + 1), L * basis d k y := by rw [← mul_sum, sum_basis, mul_one]
    _ ≤ _ := by
      apply sum_le_sum
      intro k hk
      rw [mem_range] at hk
      exact mul_le_mul_of_nonneg_right (hL k (by omega)) (basis_nonneg d k h0 h1)

end Noperthedron.PentagonalHexecontahedron.Bernstein
