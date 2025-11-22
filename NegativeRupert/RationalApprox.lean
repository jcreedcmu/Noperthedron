import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.NormNum.NatFactorial

open Nat -- for ! notation

noncomputable section

/--
Sine partial sum `x - x³/3! + x⁵/5! - ⋯` up to and including the 2n-1 degree term.
-/
def sin_psum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)

/--
Cosine partial sum `1 - x²/2! + x⁴/4! - ⋯` up to and including the 2n-2 degree term.
-/
def cos_psum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / (2 * i)!)

def sinℚ := sin_psum 13

def cosℚ := cos_psum 13

def κ : ℝ := 1 / 10^10

end

theorem sin_psum_approx (x : ℝ) (n : ℕ) : |Real.sin x - sin_psum n x| ≤ |x|^(2 * n + 1) / (2 * n + 1)! := by
  sorry

theorem cos_psum_approx (x : ℝ) (n : ℕ) : |Real.cos x - cos_psum n x| ≤ |x|^(2 * n) / (2 * n)! := by
  sorry

theorem sinℚ_approx (x : ℝ) : |Real.sin x - sinℚ x| ≤ |x|^27 / 27! :=
  sin_psum_approx x 13

theorem cosℚ_approx (x : ℝ) : |Real.cos x - cosℚ x| ≤ |x|^26 / 26! :=
  cos_psum_approx x 13

theorem sinℚ_approx' (x : ℝ) (hx : x ∈ Set.Icc (-4) 4) : |Real.sin x - sinℚ x| ≤ κ / 7 := by
  have hx' : |x| ≤ 4 := abs_le.mpr hx
  have z := sinℚ_approx x
  grw [hx'] at z
  have : 4 ^ 27 / ↑27! ≤ κ / 7 := by
    norm_num [κ]
  grw [← this]
  exact z

theorem cosℚ_approx' (x : ℝ) (hx : x ∈ Set.Icc (-4) 4) : |Real.cos x - cosℚ x| ≤ κ / 7 := by
  have hx' : |x| ≤ 4 := abs_le.mpr hx
  have z := cosℚ_approx x
  grw [hx'] at z
  have : 4 ^ 26 / ↑26! ≤ κ / 7 := by
    norm_num [κ]
  grw [← this]
  exact z

#min_imports
