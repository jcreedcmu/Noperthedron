import Mathlib.Analysis.Complex.Trigonometric

import NegativeRupert.Basic

open scoped Real

namespace Bounding

theorem one_plus_cos_mul_one_plus_cos_ge (a b : ℝ) (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    2 + 2 * Real.cos √(a ^ 2 + b ^ 2) ≤ (1 + Real.cos a) * (1 + Real.cos b) := by
  sorry

theorem norm_RxRy_minus_id_le (α β : ℝ) : ‖(RxL α).comp (RyL β) - 1‖ ≤ √(α ^ 2 + β ^ 2) := by
  sorry

theorem norm_RxRy_minus_id_eq_iff (α β : ℝ) :
    ‖(RxL α).comp (RyL β) - 1‖ = √(α ^ 2 + β ^ 2) ↔ α = 0 ∧ β = 0 := by
  sorry
