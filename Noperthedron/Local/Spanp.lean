import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Archimedean.Real.Hom

import Noperthedron.EuclideanSpaceNotation

namespace Local

open scoped RealInnerProductSpace Real

/-- The positive cone of a finite collection of vectors -/
def Spanp {n : ℕ} (v : Fin n → Euc(n)) : Set Euc(n) :=
  {w | ∃ c : Fin n → ℝ, (∀ i, 0 < c i) ∧ w = ∑ i, c i • v i }

/-- [SY25] Lemma 23 -/
theorem langles {Y Z : Euc(3)} {V : Fin 3 → Euc(3)} (hYZ : ‖Y‖ = ‖Z‖)
    (hY : Y ∈ Spanp V) (hZ : Z ∈ Spanp V) :
    ∃ i, ⟪V i, Y⟫ ≤ ⟪V i, Z⟫ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨Yco, Ypos, Ysum⟩ := hY
  obtain ⟨Zco, Zpos, Zsum⟩ := hZ
  -- Inner products against `Y` and `Z` expand along their positive combinations,
  have expandY (W : Euc(3)) : ⟪Y, W⟫ = ∑ i, Yco i * ⟪V i, W⟫ := by
    rw [Ysum, sum_inner]
    simp [real_inner_smul_left]
  have expandZ (W : Euc(3)) : ⟪Z, W⟫ = ∑ i, Zco i * ⟪V i, W⟫ := by
    rw [Zsum, sum_inner]
    simp [real_inner_smul_left]
  -- so replacing `Z` by `Y` componentwise twice gives `‖Z‖² < ⟪Y, Z⟫ < ‖Y‖²`.
  have key : ‖Z‖ ^ 2 < ‖Y‖ ^ 2 := by
    calc ‖Z‖ ^ 2 = ⟪Z, Z⟫ := (real_inner_self_eq_norm_sq Z).symm
      _ = ∑ i, Zco i * ⟪V i, Z⟫ := expandZ Z
      _ < ∑ i, Zco i * ⟪V i, Y⟫ :=
          Finset.sum_lt_sum_of_nonempty (by simp) fun i _ =>
            mul_lt_mul_of_pos_left (hlt i) (Zpos i)
      _ = ⟪Z, Y⟫ := (expandZ Y).symm
      _ = ⟪Y, Z⟫ := real_inner_comm Y Z
      _ = ∑ i, Yco i * ⟪V i, Z⟫ := expandY Z
      _ < ∑ i, Yco i * ⟪V i, Y⟫ :=
          Finset.sum_lt_sum_of_nonempty (by simp) fun i _ =>
            mul_lt_mul_of_pos_left (hlt i) (Ypos i)
      _ = ⟪Y, Y⟫ := (expandY Y).symm
      _ = ‖Y‖ ^ 2 := real_inner_self_eq_norm_sq Y
  rw [hYZ] at key
  exact lt_irrefl _ key
