import Noperthedron.RationalApprox.TrigLemmas
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Vertex approximation bounds

Proves that rotation angles lie in `[-4, 4]` after reduction,
enabling `sinℚ_approx'`/`cosℚ_approx'` for vertex error bounds.

## Angle reduction strategy

For k = 0..14, the angle `2πk/15` ranges from 0 to ~5.86.
For k > 7, `2πk/15 > 4` (outside the `sinℚ_approx'` domain).

We reduce: `k' = 15 - k` for k > 7, giving `2πk'/15 ∈ [0, 2π·7/15] ⊂ [-4, 4]`.
Then use:
- `cos(2πk/15) = cos(2πk'/15)` (cosine is even about 2π)
- `sin(2πk/15) = -sin(2πk'/15)` (sine flips about 2π)
-/

namespace Solution

open Real

/-- The reduced rotation index is always ≤ 7. -/
lemma reduceK_le_seven (k : ℕ) : (if k % 15 ≤ 7 then k % 15 else 15 - k % 15) ≤ 7 := by
  split
  · assumption
  · omega

/-- The reduced rotation angle lies in `[-4, 4]`. -/
lemma reduced_angle_in_range (k : ℕ) :
    2 * π * (↑(if k % 15 ≤ 7 then k % 15 else 15 - k % 15) : ℝ) / 15 ∈
      Set.Icc (-4 : ℝ) 4 := by
  apply angle_in_range
  exact reduceK_le_seven k

/-- The rotation angle `2πk/15` lies in `[-4, 4]` for `k ≤ 7`. -/
lemma angle_in_range (k : ℕ) (hk : k ≤ 7) :
    2 * π * (k : ℝ) / 15 ∈ Set.Icc (-4 : ℝ) 4 := by
  refine ⟨?_, ?_⟩
  · have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have : 0 < π := pi_pos
    nlinarith
  · have hk' : (k : ℝ) ≤ 7 := by exact_mod_cast hk
    have hpi : π < 4 := pi_lt_four
    nlinarith

/-! ### Numeric bounds -/

/-- √2 * κ/7 < κ — the coarsest trig-error bound is already sub-κ. -/
lemma sqrt2_kappa_div7_lt_kappa : √2 * RationalApprox.κ / 7 < RationalApprox.κ := by
  have hκ : (0 : ℝ) < RationalApprox.κ := by norm_num [RationalApprox.κ]
  have h2 : √2 < 2 := by
    have : (2 : ℝ) = √(2^2) := by rw [Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]
    rw [this]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

/-- 2√2 * κ/7 < κ — coordinate-wise bound is also sub-κ. -/
lemma two_sqrt2_kappa_div7_lt_kappa : 2 * √2 * RationalApprox.κ / 7 < RationalApprox.κ := by
  have hκ : (0 : ℝ) < RationalApprox.κ := by norm_num [RationalApprox.κ]
  have h2 : √2 < 2 := by
    have : (2 : ℝ) = √(2^2) := by rw [Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]
    rw [this]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

end Solution
