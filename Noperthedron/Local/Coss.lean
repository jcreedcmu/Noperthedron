import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Bounding
import Noperthedron.Local.Prelims

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 33 -/
theorem coss {ε θ θ_ φ φ_ : ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    let M := rotM θ φ
    let M_ := rotM θ_ φ_
    ‖M P‖ * ‖M (P - Q)‖ ≠ 0 →
     (⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
      ((‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε))
     ≤
      ⟪M P, M (P - Q)⟫ / (‖M P‖ * ‖M (P - Q)‖) := by
  intro M M_ hd
  -- We will show that the numerator of the left-hand side is bigger
  -- than the one of the righthand side, and that the factors in the denominator
  -- are smaller.
  apply div_le_div₀
  · sorry
  · -- use lemma 25
    have h₁ := Local.abs_sub_inner_le M M_ P (P - Q)
    grw [hP] at h₁
    rw [one_mul] at h₁
    grw [Bounding.norm_M_sub_lt hε hθ hφ] at h₁
    rw [Bounding.rotM_norm_one, Bounding.rotM_norm_one] at h₁
    sorry
  · positivity
  · refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity)
    · have h₁ : ‖M P‖ - √2 * ε ≤ ‖M P‖ - ‖M - M_‖ * ‖P‖ := by
         -- use lemma 13
         grw [hP, Bounding.norm_M_sub_lt hε hθ hφ]
         simp
      have h₂ : ‖M P‖ - ‖M - M_‖ * ‖P‖ ≤ ‖M P‖ - ‖M P - M_ P‖ := by
        rw [← ContinuousLinearMap.sub_apply]
        grw [←ContinuousLinearMap.le_opNorm]
      have h₃ : ‖M P‖ - ‖M P - M_ P‖ ≤ ‖M_ P‖ := by
         linarith only [norm_le_norm_add_norm_sub' (M P) (M_ P)]
      linarith
    · have h₃ : ‖P - Q‖ ≤ 2 := by
         have : ‖P - Q‖ ≤ ‖P‖ + ‖Q‖ := norm_sub_le P Q
         linarith
      have h₁ : ‖M (P - Q)‖ - 2 * √2 * ε ≤ ‖M (P - Q)‖ - ‖M - M_‖ * ‖P - Q‖ := by
        grw [h₃, Bounding.norm_M_sub_lt hε hθ hφ]
        linarith only
      have h₂ : ‖M (P - Q)‖ - ‖M - M_‖ * ‖P - Q‖ ≤ ‖M_ (P - Q)‖ := by
        grw [←ContinuousLinearMap.le_opNorm]
        rw [ContinuousLinearMap.sub_apply]
        linarith only [norm_le_norm_add_norm_sub' (M (P - Q)) (M_ (P - Q))]
      linarith only [h₁, h₂]

