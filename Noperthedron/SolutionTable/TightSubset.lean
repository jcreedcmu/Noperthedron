import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.RationalLocalCheck.Precondition
import Noperthedron.PoseInterval
import Mathlib.Analysis.Real.Pi.Bounds

namespace Solution

open scoped Real

/--
The tight interval is contained in the pose interval derived from any `Solution.Interval`
whose integer bounds are at least as wide as row 0 of the solution table.

The numeric bounds follow from `π < 3.15` (`Real.pi_lt_d2`).
-/
theorem tightSubset_of_intervals
    (iv : Solution.Interval)
    (hθ₁_lo : iv.min .θ₁ ≤ 0) (hθ₁_hi : 6451200 ≤ iv.max .θ₁)
    (hφ₁_lo : iv.min .φ₁ ≤ 0) (hφ₁_hi : 48384000 ≤ iv.max .φ₁)
    (hθ₂_lo : iv.min .θ₂ ≤ 0) (hθ₂_hi : 6451200 ≤ iv.max .θ₂)
    (hφ₂_lo : iv.min .φ₂ ≤ 0) (hφ₂_hi : 24268800 ≤ iv.max .φ₂)
    (hα_lo : iv.min .α ≤ -24268800) (hα_hi : 24268800 ≤ iv.max .α) :
    tightInterval ⊆ iv.toPoseInterval := by
  intro q hq
  -- Decompose membership in tightInterval via PoseInterval.contains
  -- Order in PoseInterval.contains: θ₁, θ₂, φ₁, φ₂, α
  simp only [Membership.mem, PoseInterval.contains,
    tightInterval, Interval.toPoseInterval] at hq ⊢
  obtain ⟨hq_θ₁, hq_θ₂, hq_φ₁, hq_φ₂, hq_α⟩ := hq
  -- Useful constants
  have hDval : DENOM = (15360000 : ℝ) := rfl
  have hD : (0 : ℝ) < DENOM := by norm_num [DENOM]
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  -- Cast integer hypotheses to ℝ
  have hθ₁_lo_r : (iv.min .θ₁ : ℝ) ≤ 0 := by exact_mod_cast hθ₁_lo
  have hθ₁_hi_r : (6451200 : ℝ) ≤ (iv.max .θ₁ : ℝ) := by exact_mod_cast hθ₁_hi
  have hφ₁_lo_r : (iv.min .φ₁ : ℝ) ≤ 0 := by exact_mod_cast hφ₁_lo
  have hφ₁_hi_r : (48384000 : ℝ) ≤ (iv.max .φ₁ : ℝ) := by exact_mod_cast hφ₁_hi
  have hθ₂_lo_r : (iv.min .θ₂ : ℝ) ≤ 0 := by exact_mod_cast hθ₂_lo
  have hθ₂_hi_r : (6451200 : ℝ) ≤ (iv.max .θ₂ : ℝ) := by exact_mod_cast hθ₂_hi
  have hφ₂_lo_r : (iv.min .φ₂ : ℝ) ≤ 0 := by exact_mod_cast hφ₂_lo
  have hφ₂_hi_r : (24268800 : ℝ) ≤ (iv.max .φ₂ : ℝ) := by exact_mod_cast hφ₂_hi
  have hα_lo_r : (iv.min .α : ℝ) ≤ -24268800 := by exact_mod_cast hα_lo
  have hα_hi_r : (24268800 : ℝ) ≤ (iv.max .α : ℝ) := by exact_mod_cast hα_hi
  -- For each coordinate, show Icc containment via transitivity of bounds
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  -- θ₁ lower: iv.min.θ₁ / DENOM ≤ q.θ₁
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hθ₁_lo_r (le_of_lt hD)) hq_θ₁.1
  -- θ₁ upper: q.θ₁ ≤ iv.max.θ₁ / DENOM
  · apply le_trans hq_θ₁.2
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 15) hD]
    -- Goal: 2 * π * DENOM ≤ iv.max.θ₁ * 15
    nlinarith [hDval]
  -- θ₂ lower: iv.min.θ₂ / DENOM ≤ q.θ₂
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hθ₂_lo_r (le_of_lt hD)) hq_θ₂.1
  -- θ₂ upper: q.θ₂ ≤ iv.max.θ₂ / DENOM
  · apply le_trans hq_θ₂.2
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 15) hD]
    nlinarith [hDval]
  -- φ₁ lower: iv.min.φ₁ / DENOM ≤ q.φ₁
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hφ₁_lo_r (le_of_lt hD)) hq_φ₁.1
  -- φ₁ upper: q.φ₁ ≤ iv.max.φ₁ / DENOM
  · apply le_trans hq_φ₁.2
    rw [le_div_iff₀ hD]
    -- Goal: π * DENOM ≤ iv.max.φ₁
    nlinarith [hDval]
  -- φ₂ lower: iv.min.φ₂ / DENOM ≤ q.φ₂
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hφ₂_lo_r (le_of_lt hD)) hq_φ₂.1
  -- φ₂ upper: q.φ₂ ≤ iv.max.φ₂ / DENOM
  · apply le_trans hq_φ₂.2
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2) hD]
    -- Goal: π * DENOM ≤ iv.max.φ₂ * 2
    nlinarith [hDval]
  -- α lower: iv.min.α / DENOM ≤ q.α
  · apply le_trans _ hq_α.1
    rw [div_le_iff₀ hD]
    -- Goal: iv.min.α ≤ -(π / 2) * DENOM
    nlinarith [hDval]
  -- α upper: q.α ≤ iv.max.α / DENOM
  · apply le_trans hq_α.2
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2) hD]
    -- Goal: π * DENOM ≤ iv.max.α * 2
    nlinarith [hDval]

end Solution