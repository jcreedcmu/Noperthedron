import Mathlib.Analysis.InnerProductSpace.PiL2

import NegativeRupert.Basic

namespace Local

open scoped RealInnerProductSpace Real

notation "Euc(" n:arg ")" => EuclideanSpace ℝ (Fin n)

theorem abs_sub_inner_bars_le {n : ℕ} (A B A_ B_ : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, B P₂⟫ - ⟪A_ P₁, B_ P₂⟫| ≤
    ‖P₁‖ * ‖P₂‖ * (‖A - A_‖ * ‖B‖ + ‖A_‖ * ‖B - B_‖ + ‖A - A_‖ * ‖A - B_‖) := by
  sorry

theorem abs_sub_inner_le {n : ℕ} (A B : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤ ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (‖A‖ + ‖B‖ + ‖A - B‖) := by
  sorry

theorem origin_in_triangle {A B C : Euc(2)}
    (hA : 0 < ⟪rotR (π/2) A, B⟫) (hB : 0 < ⟪rotR (π/2) B, C⟫) (hC : 0 < ⟪rotR (π/2) C, A⟫) :
    0 ∈ interior (convexHull ℝ {A, B, C}) := by
  sorry

structure Spanning (θ φ ε : ℝ) (P₁ P₂ P₃ : Euc(3)) : Prop where
  pos : 0 < ε
  lt1 : 2 * ε * (√2 + ε) <  ⟪rotR (π / 2) (rotM θ φ P₁), rotM θ φ P₂⟫
  lt2 : 2 * ε * (√2 + ε) <  ⟪rotR (π / 2) (rotM θ φ P₂), rotM θ φ P₃⟫
  lt3 : 2 * ε * (√2 + ε) <  ⟪rotR (π / 2) (rotM θ φ P₃), rotM θ φ P₁⟫
