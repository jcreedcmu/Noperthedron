import Mathlib.Analysis.Complex.Trigonometric

open scoped Real

namespace Bounding

theorem one_plus_cos_mul_one_plus_cos_ge (a b : ℝ) (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    2 + 2 * Real.cos √(a ^ 2 + b ^ 2) ≤ (1 + Real.cos a) * (1 + Real.cos b) := by
  sorry
