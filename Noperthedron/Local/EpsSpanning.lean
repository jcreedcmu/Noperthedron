import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Bounding
import Noperthedron.Local.Prelims
import Noperthedron.Local.OriginInTriangle
import Noperthedron.Local.Spanp

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

def Triangle : Type := Fin 3 → ℝ³

/-- The triangle P is congruent to Q in the usual geometric sense -/
def Triangle.Congruent (P Q : Triangle) : Prop := by
  sorry

/-- [SY25] Definition 27. Note that the "+ 1" at the type Fin 3 wraps. -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℝ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) < ⟪rotR (π / 2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫

lemma triangle_ineq_aux
    {d x y : ℝ} (hd : 0 < d) (hy : d < y) (hx : |x - y| ≤ d) : 0 < x := by
  grind

/-- [SY25] Lemma 28 -/
theorem vecX_spanning {ε θ θ_ φ φ_ : ℝ} (P : Triangle)
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hSpanning: P.Spanning θ_ φ_ ε)
    (hP : ∀ i, ‖P i‖ ≤ 1)
    (hX : ∀ i, 0 < ⟪vecX θ φ, P i⟫) :
    vecX θ φ ∈ Spanp P := by
  obtain ⟨hε, hlt⟩ := hSpanning
  have h₁ : ∀ i, 0 < ⟪rotR (π/2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫ := by
    intro i
    -- lemma 24 -> Local.abs_sub_inner_bars_le
    have h₂ :=
      Local.abs_sub_inner_bars_le
        (rotR (π/2) ∘L rotM θ φ) (rotM θ φ)
        (rotR (π/2) ∘L rotM θ_ φ_) (rotM θ_ φ_)
        (P i) (P (i + 1))

    specialize hlt i

    rw [←ContinuousLinearMap.comp_sub] at h₂
    grw [hP, hP] at h₂
    grw [ContinuousLinearMap.opNorm_comp_le (rotR (π / 2)) (rotM θ_ φ_)] at h₂
    grw [ContinuousLinearMap.opNorm_comp_le] at h₂
    simp only [Bounding.rotR_norm_one, Bounding.rotM_norm_one, mul_one, one_mul] at h₂

    -- lemma 13 -> Bounding.norm_M_sub_lt
    have h₃ := Bounding.norm_M_sub_lt hε hθ hφ
    grw [h₃] at h₂
    have h₄ : √2 * ε + √2 * ε + √2 * ε * (√2 * ε) = 2 * ε * (√2 + ε) := by
      rw [show √2 * ε * (√2 * ε) = √2^2 * ε^2 by ring]
      simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
      ring
    rw [h₄] at h₂
    clear h₃ h₄
    have hd : 0 < 2 * ε * (√2 + ε) := by positivity
    exact triangle_ineq_aux hd hlt h₂
  sorry


/-
  |⟪((rotR (π / 2)).comp (rotM θ φ)) (P i), (rotM θ φ) (P (i + 1))⟫ -
        ⟪((rotR (π / 2)).comp (rotM θ_ φ_)) (P i), (rotM θ_ φ_) (P (i + 1))⟫| ≤
    ‖rotM θ φ - rotM θ_ φ_‖ + ‖rotM θ φ - rotM θ_ φ_‖ + ‖rotM θ φ - rotM θ_ φ_‖ * ‖rotM θ φ - rotM θ_ φ_‖
-/
