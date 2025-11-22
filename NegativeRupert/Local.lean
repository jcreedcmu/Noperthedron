import Mathlib.Analysis.InnerProductSpace.PiL2

import NegativeRupert.Basic

namespace Local

open scoped RealInnerProductSpace Real

notation "Euc(" n:arg ")" => EuclideanSpace ℝ (Fin n)

-- TODO: The WithLp.toLP conversion below is awkward. To we have a nicer way
-- to get a handle on that conversion?
theorem pythagoras {θ φ : ℝ} (P : Euc(3)) :
    ‖rotM θ φ P‖ ^ 2 = ‖P‖ ^ 2 - ⟪rotX θ φ (WithLp.toLp 2 fun _ ↦ 1), P⟫ ^ 2 := by
  sorry

def spanp {n : ℕ} (v : Fin n → Euc(n)) : Set Euc(n) :=
  {w | ∃ c : Fin n → ℝ, ∀ i, 0 < c i ∧ w = ∑ i, c i • v i }

theorem langles {Y Z : Euc(3)} {V : Fin 3 → Euc(3)} (hYZ : ‖Y‖ = ‖Z‖)
    (hY : Y ∈ spanp V) (hZ : Z ∈ spanp V) :
    ⟪V 0, Y⟫ ≤ ⟪V 0, Z⟫ ∨ ⟪V 1, Y⟫ ≤ ⟪V 1, Z⟫ ∨ ⟪V 2, Y⟫ ≤ ⟪V 2, Z⟫ := by
  sorry

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

theorem rotX_spanning {ε θ θ_ φ φ_ : ℝ} (P : Fin 3 → Euc(3))
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hSpanning: Spanning θ_ φ_ ε (P 1) (P 2) (P 3))
    (hX : ∀ i, 0 < ⟪rotX θ φ (WithLp.toLp 2 fun _ ↦ 1), P i⟫) :
    rotX θ φ (WithLp.toLp 2 fun _ ↦ 1) ∈ spanp P := by
  sorry

theorem coss {ε θ θ_ φ φ_ : ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    let M := rotM θ φ
    let M_ := rotM θ_ φ_
    (⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
     ((‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε))
    ≤
     ⟪M P, M (P - Q)⟫ / (‖M P‖ * ‖M (P - Q)‖):= by
  sorry
