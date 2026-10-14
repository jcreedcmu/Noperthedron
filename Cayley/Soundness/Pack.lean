module

public import Mathlib

@[expose] public section

/-!
# Slot-packed natural numbers

`packN W d n = Σ_{j < n} d j · 2^(W j)`. When every digit is below `2^W`, bitwise `and`, shifts,
slot-wise sums and differences, and horizontal sums (`mod 2^W - 1`) act digit by digit.
-/

namespace Cayley.Pack

/-- `Σ_{j < n} d j · 2^(W j)`. -/
def packN (W : ℕ) (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packN W d n + d n * 2 ^ (W * n)

variable {W : ℕ} {d e : ℕ → ℕ} {n : ℕ}

theorem packN_succ (n : ℕ) : packN W d (n + 1) = packN W d n + d n * 2 ^ (W * n) := rfl

theorem packN_eq_sum : packN W d n = ∑ j ∈ Finset.range n, d j * 2 ^ (W * j) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packN_succ, ih, Finset.sum_range_succ]

theorem packN_lt (hd : ∀ j < n, d j < 2 ^ W) : packN W d n < 2 ^ (W * n) := by
  induction n with
  | zero => simp [packN]
  | succ n ih =>
    rw [packN_succ, Nat.mul_succ, pow_add]
    have h1 := ih (fun j hj => hd j (by omega))
    have h2 : d n + 1 ≤ 2 ^ W := hd n (by omega)
    calc packN W d n + d n * 2 ^ (W * n) < 2 ^ (W * n) + d n * 2 ^ (W * n) := by omega
      _ = (d n + 1) * 2 ^ (W * n) := by ring
      _ ≤ 2 ^ W * 2 ^ (W * n) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (W * n) * 2 ^ W := by ring

theorem testBit_packN (hd : ∀ j < n, d j < 2 ^ W) (k : ℕ) :
    (packN W d n).testBit k = (decide (k < W * n) && (d (k / W)).testBit (k % W)) := by
  induction n with
  | zero => simp [packN]
  | succ n ih =>
    have ih' := ih (fun j hj => hd j (by omega))
    have hlt := packN_lt (W := W) (d := d) (n := n) (fun j hj => hd j (by omega))
    rw [packN_succ, add_comm, mul_comm, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hk : k < W * n
    · have hk' : k < W * (n + 1) := lt_of_lt_of_le hk (Nat.mul_le_mul_left _ (by omega))
      simp only [hk, ↓reduceIte, ih', decide_true, hk']
    · simp only [hk, ↓reduceIte]
      by_cases hk2 : k < W * (n + 1)
      · have hq : k / W = n := Nat.div_eq_of_lt_le (by rw [mul_comm]; omega)
          (by rw [mul_comm]; exact hk2)
        have hr : k % W = k - W * n := by
          have := Nat.div_add_mod k W; rw [hq] at this; omega
        rw [decide_eq_true hk2, hq, hr, Bool.true_and]
      · rw [decide_eq_false hk2, Bool.false_and]
        apply Nat.testBit_lt_two_pow
        calc d n < 2 ^ W := hd n (by omega)
          _ ≤ 2 ^ (k - W * n) := Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ] at hk2; omega)

theorem packN_land (hW : 0 < W) (hd : ∀ j < n, d j < 2 ^ W) (he : ∀ j < n, e j < 2 ^ W) :
    packN W d n &&& packN W e n = packN W (fun j => d j &&& e j) n := by
  have hde : ∀ j < n, (d j &&& e j) < 2 ^ W := fun j hj => Nat.and_lt_two_pow _ (he j hj)
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_land, testBit_packN hd, testBit_packN he, testBit_packN hde,
    Nat.testBit_land]
  cases decide (k < W * n) <;> simp

theorem packN_add : packN W (fun j => d j + e j) n = packN W d n + packN W e n := by
  simp only [packN_eq_sum, add_mul, Finset.sum_add_distrib]

theorem packN_sub (h : ∀ j < n, e j ≤ d j) :
    packN W (fun j => d j - e j) n = packN W d n - packN W e n := by
  have : packN W d n = packN W (fun j => d j - e j) n + packN W e n := by
    rw [← packN_add]
    simp only [packN_eq_sum]
    exact Finset.sum_congr rfl fun j hj => by rw [Nat.sub_add_cancel (h j (Finset.mem_range.1 hj))]
  omega

theorem packN_mul_left (c : ℕ) : c * packN W d n = packN W (fun j => c * d j) n := by
  simp only [packN_eq_sum, Finset.mul_sum, mul_assoc]

theorem packN_congr (h : ∀ j < n, d j = e j) : packN W d n = packN W e n := by
  simp only [packN_eq_sum]
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

/-- Slot `0` of a packed number. -/
theorem packN_land_low (hW : 0 < W) (hd : ∀ j < n, d j < 2 ^ W) (hn : 0 < n) :
    packN W d n &&& (2 ^ W - 1) = d 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_land, testBit_packN hd, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < W
  · have hkn : k < W * n := lt_of_lt_of_le hk (Nat.le_mul_of_pos_right W hn)
    rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
    simp [hk, hkn]
  · simp only [hk, decide_false, Bool.and_false]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (hd 0 hn)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

/-- The top bit of every slot, moved to the slot's bottom. -/
theorem packN_signs (hW : 0 < W) (hd : ∀ j < n, d j < 2 ^ W) :
    (packN W d n >>> (W - 1)) &&& packN W (fun _ => 1) n =
      packN W (fun j => d j / 2 ^ (W - 1)) n := by
  have h1 : ∀ j < n, (fun _ => 1) j < 2 ^ W := fun _ _ => Nat.one_lt_two_pow (by omega)
  have hq : ∀ j < n, d j / 2 ^ (W - 1) < 2 ^ W := fun j hj =>
    lt_of_le_of_lt (Nat.div_le_self _ _) (hd j hj)
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_land, Nat.testBit_shiftRight, testBit_packN hd, testBit_packN h1,
    testBit_packN hq, Nat.testBit_div_two_pow]
  by_cases hk : k < W * n
  · have hkW : k % W < W := Nat.mod_lt _ hW
    have hqn : k / W < n := by rw [Nat.div_lt_iff_lt_mul hW, mul_comm]; exact hk
    by_cases h0 : k % W = 0
    · have hkk : W - 1 + k < W * n := by
        have h1 := Nat.div_add_mod k W
        have h2 : W * (k / W + 1) ≤ W * n := Nat.mul_le_mul_left _ hqn
        rw [mul_add] at h2
        omega
      have hdiv : (W - 1 + k) / W = k / W := by
        rw [show W - 1 + k = (W - 1) + W * (k / W) by have := Nat.div_add_mod k W; omega,
          Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt (by omega), zero_add]
      have hmod : (W - 1 + k) % W = W - 1 := by
        rw [show W - 1 + k = (W - 1) + W * (k / W) by have := Nat.div_add_mod k W; omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      simp [hk, hkk, h0, hdiv, hmod, Nat.testBit_zero]
    · have h1 : Nat.testBit 1 (k % W) = false :=
        Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      have h2 : (d (k / W)).testBit (k % W + (W - 1)) = false := by
        apply Nat.testBit_lt_two_pow
        calc d (k / W) < 2 ^ W := hd _ hqn
          _ ≤ 2 ^ (k % W + (W - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp [hk, h1, h2]
  · simp [hk]

/-- Horizontal sum: `2^W ≡ 1 [MOD 2^W - 1]`. -/
theorem packN_mod (hd : (∑ j ∈ Finset.range n, d j) < 2 ^ W - 1) :
    packN W d n % (2 ^ W - 1) = ∑ j ∈ Finset.range n, d j := by
  rw [← Nat.mod_eq_of_lt hd, packN_eq_sum]
  apply Nat.ModEq.sum
  intro j _
  have h : 2 ^ W ≡ 1 [MOD 2 ^ W - 1] :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 dvd_rfl).symm
  calc d j * 2 ^ (W * j) ≡ d j * 1 ^ j [MOD 2 ^ W - 1] := by
        rw [pow_mul]; exact Nat.ModEq.mul_left _ (Nat.ModEq.pow _ h)
    _ = d j := by simp

end Cayley.Pack

end
