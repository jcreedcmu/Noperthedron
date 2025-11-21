import Mathlib.Analysis.InnerProductSpace.PiL2

import NegativeRupert.Basic

namespace Local

open scoped RealInnerProductSpace

notation "Euc(" n:arg ")" => EuclideanSpace ℝ (Fin n)

theorem abs_sub_inner_bars_le {n : ℕ} (A B A_ B_ : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, B P₂⟫ - ⟪A_ P₁, B_ P₂⟫| ≤
    ‖P₁‖ * ‖P₂‖ * (‖A - A_‖ * ‖B‖ + ‖A_‖ * ‖B - B_‖ + ‖A - A_‖ * ‖A - B_‖) := by
  sorry

theorem abs_sub_inner_le {n : ℕ} (A B : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤ ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (‖A‖ + ‖B‖ + ‖A - B‖) := by
  sorry
