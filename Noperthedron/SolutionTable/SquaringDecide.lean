import Noperthedron.SolutionTable.Validity
import Noperthedron.RationalApprox.EpsKapSpanning

/-!
# Squaring trick for eliminating √2 from decidable comparisons

The key identities used:
- `q > √2 * r + s ↔ q - s > 0 ∧ (q - s)² > 2 * r²` (when r ≥ 0)
- `q > 2 * r * √2 + s ↔ q - s > 0 ∧ (q - s)² > 8 * r²` (when r ≥ 0)

These eliminate √2 from comparisons, making them decidable over ℚ.
-/

namespace Solution

open Real
open scoped RealInnerProductSpace

/-! ### Core squaring lemma -/

/-- Squaring trick: `q > √2 * r + s` with `r ≥ 0` iff `q > s` and `(q-s)² > 2r²`. -/
theorem gt_sqrt2_mul_add_iff {q r s : ℝ} (hr : 0 ≤ r) :
    q > √2 * r + s ↔ q - s > 0 ∧ (q - s) ^ 2 > 2 * r ^ 2 := by
  constructor
  · intro h
    constructor
    · linarith [Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) hr]
    · have hqs : q - s > 0 := by
        linarith [Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) hr]
      have hsq : √2 * r < q - s := by linarith
      have h2 : (√2 * r) ^ 2 < (q - s) ^ 2 := by
        exact sq_lt_sq' (by linarith [mul_nonneg (Real.sqrt_nonneg 2) hr]) hsq
      simp [mul_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)] at h2
      linarith
  · rintro ⟨hqs, hsq⟩
    -- Need: q > √2 * r + s, i.e., q - s > √2 * r
    -- We know (q-s)² > 2r² and q - s > 0
    by_contra h
    push_neg at h
    -- h : q ≤ √2 * r + s, so q - s ≤ √2 * r
    have hle : q - s ≤ √2 * r := by linarith
    have : (q - s) ^ 2 ≤ (√2 * r) ^ 2 := by
      exact sq_le_sq' (by linarith [mul_nonneg (Real.sqrt_nonneg 2) hr]) hle
    simp [mul_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)] at this
    linarith

/-- Variant for `q > 2 * ε * √2 + s`, used in κSpanning. -/
theorem gt_two_mul_sqrt2_add_iff {q ε s : ℝ} (hε : 0 ≤ ε) :
    q > 2 * ε * √2 + s ↔ q - s > 0 ∧ (q - s) ^ 2 > 8 * ε ^ 2 := by
  have : 2 * ε * √2 = √2 * (2 * ε) := by ring
  rw [this, gt_sqrt2_mul_add_iff (by linarith)]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith⟩

end Solution
