import Noperthedron.RationalApprox.TrigLemmas
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Vertex approximation bound

Proves that `2πk/15 ∈ [-4, 4]` for `k ≤ 7`, enabling application of
`sinℚ_approx'` and `cosℚ_approx'` to bound the trig approximation error
for noperthedron vertex rotation angles.

This is the first building block for proving `‖indexPoint - approxVertex‖ ≤ κ`.
-/

namespace Solution

open Real

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

end Solution
