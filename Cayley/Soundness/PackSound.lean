module

public import Cayley.Soundness.PackDecode

@[expose] public section

/-!
# The checker's packed bounds are sound

`pLower`, `qLower` and `pStats` (layouts `L3`, `L5` of `Cayley.Checker.KPack`) bound polynomial
expressions that fit the layout and have coefficient norm below `2^(PW-1)`.
-/

namespace Cayley.Pack

set_option exponentiation.threshold 1024

open Cayley.K

/-- Radix 3 in every variable. -/
def L3 : Layout := ⟨fun _ => 3, ![1, 3, 9, 27, 81], 243⟩

/-- Radix 5 in `t₀, t₁`, 3 in the others. -/
def L5 : Layout := ⟨![5, 5, 3, 3, 3], ![1, 5, 25, 75, 225], 675⟩

/-- The mixed-radix facts as a Boolean check. -/
def goodB (L : Layout) : Bool :=
  (List.range L.n).all (fun j => L.idx (L.dig j) == j) &&
  (List.range (L.r 0)).all fun a0 => (List.range (L.r 1)).all fun a1 =>
    (List.range (L.r 2)).all fun a2 => (List.range (L.r 3)).all fun a3 =>
      (List.range (L.r 4)).all fun a4 =>
        decide (L.idx ![a0, a1, a2, a3, a4] < L.n) &&
          (List.finRange 5).all fun i => L.dig (L.idx ![a0, a1, a2, a3, a4]) i == ![a0, a1, a2, a3, a4] i

theorem good_of (L : Layout) (h : goodB L = true) : L.Good := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, List.mem_finRange, true_implies] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun m hm => ?_⟩
  have hm' : m = ![m 0, m 1, m 2, m 3, m 4] := by
    funext i; fin_cases i <;> rfl
  rw [hm']
  exact h2 _ (hm 0) _ (hm 1) _ (hm 2) _ (hm 3) _ (hm 4)

theorem L3_good : L3.Good := good_of L3 (by decide +kernel)
theorem L5_good : L5.Good := good_of L5 (by decide +kernel)

theorem onesL3_eq : onesL3 = packN PW (fun _ => 1) L3.n := by decide +kernel
theorem evensL3_eq : evensL3 = packN PW (evI L3) L3.n := by decide +kernel
theorem onesL5_eq : onesL5 = packN PW (fun _ => 1) L5.n := by decide +kernel
theorem evensL5_eq : evensL5 = packN PW (evI L5) L5.n := by decide +kernel

theorem pX_eq : (fun i : Fin 5 => pX i) = kron L3 := by
  funext i
  rw [pX, kron, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  fin_cases i <;> rfl

theorem qX_eq : (fun i : Fin 5 => qX i) = kron L5 := by
  funext i
  rw [qX, kron, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  fin_cases i <;> rfl

theorem sum_lt_of_nrm {L : Layout} (hL : L.Good) {e : PE} (h : L.Fits e) (hb : e.nrm < O) :
    (∀ j < L.n, |L.cf e j| < O) ∧ ∑ j ∈ Finset.range L.n, |L.cf e j| < (pM : ℤ) := by
  have hs := Layout.sum_abs_cf_le hL h
  have hO : (O : ℤ) < pM := by
    have : O < pM := by
      have h2 : 2 ^ PW = 2 * O := by rw [O, ← pow_succ']; rfl
      have h1 : 1 < O := Nat.one_lt_two_pow (by decide)
      rw [pM_eq, h2]; omega
    exact_mod_cast this
  have hb' : (e.nrm : ℤ) < O := by exact_mod_cast hb
  exact ⟨fun j _ => lt_of_le_of_lt (Layout.abs_cf_le j) hb', lt_of_le_of_lt hs (hb'.trans hO)⟩

/-- The packed lower bound (layout `L3`). -/
theorem pLower_le {e : PE} (h : L3.Fits e) (hb : e.nrm < O) {t : Fin 5 → ℝ}
    (ht : ∀ i, |t i| ≤ 1) : (pLower (e.ev fun i => pX i) : ℝ) ≤ e.ev t := by
  obtain ⟨hc, hS⟩ := sum_lt_of_nrm L3_good h hb
  rw [pLower, onesL3_eq, evensL3_eq, pX_eq, pLowerL_eq L3_good h (by decide) hc hS]
  exact lower_le_ev L3_good h (by decide) ht

/-- The packed lower bound (layout `L5`). -/
theorem qLower_le {e : PE} (h : L5.Fits e) (hb : e.nrm < O) {t : Fin 5 → ℝ}
    (ht : ∀ i, |t i| ≤ 1) : (qLower (e.ev fun i => qX i) : ℝ) ≤ e.ev t := by
  obtain ⟨hc, hS⟩ := sum_lt_of_nrm L5_good h hb
  rw [qLower, onesL5_eq, evensL5_eq, qX_eq, pLowerL_eq L5_good h (by decide) hc hS]
  exact lower_le_ev L5_good h (by decide) ht

/-- The packed statistics (layout `L3`). -/
theorem pStats_sound {e : PE} (h : L3.Fits e) (hb : e.nrm < O) {t : Fin 5 → ℝ}
    (ht : ∀ i, |t i| ≤ 1) :
    let st := pStats (e.ev fun i => pX i)
    (st.c0 : ℝ) - st.slack ≤ e.ev t ∧ |e.ev t - st.c0| ≤ st.abs := by
  obtain ⟨hc, hS⟩ := sum_lt_of_nrm L3_good h hb
  intro st
  have hst : st = pStatsL (packN PW (fun _ => 1) L3.n) (packN PW (evI L3) L3.n) (e.ev (kron L3)) := by
    simp only [st, pStats, onesL3_eq, evensL3_eq, pX_eq]
  obtain ⟨h1, h2, h3⟩ := pStatsL_eq L3_good h (by decide) hc hS
  rw [hst, h1, h2, h3]
  refine ⟨?_, abs_ev_sub_le L3_good h (by decide) ht⟩
  have := lower_le_ev L3_good h (by decide) ht
  push_cast at this
  exact this

end Cayley.Pack

end
