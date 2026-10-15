module

public import Cayley.Soundness.Pack
public import Cayley.Checker.KPack

@[expose] public section

/-!
# The vertex-packed tables of the gap checker

The tables `tpx … taz` hold one 640-bit slot per outer vertex. `vtxSplit` visits exactly the
vertices whose slot sign bit is set.
-/

namespace Cayley.Pack

set_option exponentiation.threshold 1024

open Cayley.K

/-- Vertex `t` of the kernel table. -/
def vt (t : ℕ) : ℤ × ℤ × ℤ := vtxI.getD t (0, 0, 0)

/-- The slot offset of the tables. -/
def BT : ℕ := 2 ^ 170

theorem tpx_eq : tpx = packN 640 (fun t => ((vt t).1 + BT).toNat) 90 := by decide +kernel
theorem tpy_eq : tpy = packN 640 (fun t => ((vt t).2.1 + BT).toNat) 90 := by decide +kernel
theorem tpz_eq : tpz = packN 640 (fun t => ((vt t).2.2 + BT).toNat) 90 := by decide +kernel
theorem tnx_eq : tnx = packN 640 (fun t => ((BT : ℤ) - (vt t).1).toNat) 90 := by decide +kernel
theorem tny_eq : tny = packN 640 (fun t => ((BT : ℤ) - (vt t).2.1).toNat) 90 := by decide +kernel
theorem tnz_eq : tnz = packN 640 (fun t => ((BT : ℤ) - (vt t).2.2).toNat) 90 := by decide +kernel
theorem tax_eq : tax = packN 640 (fun t => BT - (vt t).1.natAbs) 90 := by decide +kernel
theorem tay_eq : tay = packN 640 (fun t => BT - (vt t).2.1.natAbs) 90 := by decide +kernel
theorem taz_eq : taz = packN 640 (fun t => BT - (vt t).2.2.natAbs) 90 := by decide +kernel
theorem onesT_eq : onesT = packN 640 (fun _ => 1) 90 := by decide +kernel

/-- The vertex coordinates are below `2^161` in absolute value. -/
theorem vt_bound : ∀ t < 90, (vt t).1.natAbs < 2 ^ 161 ∧ (vt t).2.1.natAbs < 2 ^ 161 ∧
    (vt t).2.2.natAbs < 2 ^ 161 := by decide +kernel

/-- Slot extraction from a packed number. -/
theorem shiftRight_land_packN {W : ℕ} {d : ℕ → ℕ} {n : ℕ} (hd : ∀ j < n, d j < 2 ^ W) {t : ℕ}
    (ht : t < n) : Nat.land (Nat.shiftRight (packN W d n) (W * t)) (2 ^ W - 1) = d t := by
  apply Nat.eq_of_testBit_eq
  intro k
  change ((packN W d n >>> (W * t)) &&& (2 ^ W - 1)).testBit k = _
  rw [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, testBit_packN hd]
  by_cases hk : k < W
  · have h1 : W * t + k < W * n := by
      have : W * (t + 1) ≤ W * n := Nat.mul_le_mul_left _ ht
      rw [Nat.mul_succ] at this; omega
    have h2 : (W * t + k) / W = t := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hk, zero_add]
    have h3 : (W * t + k) % W = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    simp [h1, h2, h3, hk]
  · simp only [hk, decide_false, Bool.and_false]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (hd t ht)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem slot_eq {d : ℕ → ℕ} (hd : ∀ j < 90, d j < 2 ^ 640) {t : ℕ} (ht : t < 90) :
    slot (packN 640 d 90) t = d t := by
  unfold slot; rw [shiftRight_land_packN hd ht]

theorem testBit_signT {t : ℕ} (ht : t < 90) : signT.testBit (640 * t + 639) = true := by
  have h1 : ∀ j < 90, (fun _ => 1) j < 2 ^ 640 := fun _ _ => Nat.one_lt_two_pow (by norm_num)
  change (onesT <<< 639).testBit _ = true
  rw [Nat.testBit_shiftLeft, onesT_eq, testBit_packN h1]
  have h2 : 640 * t + 639 - 639 = 640 * t := by omega
  simp [h2, Nat.mul_mod_right]
  omega

/-- A vertex either passes the packed test or its fail bit is set. -/
theorem testBit_fails (V : ℕ) {t : ℕ} (ht : t < 90) :
    (Nat.xor signT (Nat.land V signT)).testBit (640 * t + 639) = !V.testBit (640 * t + 639) := by
  change (signT ^^^ (V &&& signT)).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_land, testBit_signT ht]
  cases V.testBit (640 * t + 639) <;> rfl

/-- `vtxSplit` visits every vertex whose bit is set. -/
theorem vtxSplit_sound (f : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Bool) :
    ∀ (depth lo n m : ℕ), vtxSplit f depth lo n m = true → ∀ i < n,
      m.testBit (640 * i + 639) = true →
      f (lo + i) (slot tpx (lo + i) - (2 ^ 170 : ℕ)) (slot tpy (lo + i) - (2 ^ 170 : ℕ))
        (slot tpz (lo + i) - (2 ^ 170 : ℕ)) ((2 ^ 170 : ℕ) - slot tax (lo + i))
        ((2 ^ 170 : ℕ) - slot tay (lo + i)) ((2 ^ 170 : ℕ) - slot taz (lo + i)) = true := by
  intro depth
  induction depth with
  | zero =>
    intro lo n m h i _ hb
    simp only [vtxSplit, beq_iff_eq] at h
    subst h; simp at hb
  | succ d ih =>
    intro lo n m h i hi hb
    simp only [vtxSplit] at h
    by_cases hm : m = 0
    · subst hm; simp at hb
    · simp only [beq_iff_eq, hm, ↓reduceIte] at h
      by_cases hn : n ≤ 1
      · simp only [hn, ↓reduceIte] at h
        have hi0 : i = 0 := by omega
        subst hi0
        simpa using h
      · simp only [hn, ↓reduceIte, Bool.and_eq_true] at h
        obtain ⟨hl, hr⟩ := h
        by_cases hih : i < n / 2
        · apply ih lo (n / 2) _ hl i hih
          change (m &&& (2 ^ (640 * (n / 2)) - 1)).testBit _ = true
          rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one, hb]
          simp only [Bool.true_and, decide_eq_true_eq]
          have : 640 * (i + 1) ≤ 640 * (n / 2) := Nat.mul_le_mul_left _ hih
          omega
        · have h1 := ih (lo + n / 2) (n - n / 2) _ hr (i - n / 2) (by omega) (by
            change (m >>> (640 * (n / 2))).testBit _ = true
            rw [Nat.testBit_shiftRight]
            have : 640 * (n / 2) + (640 * (i - n / 2) + 639) = 640 * i + 639 := by
              have : n / 2 ≤ i := by omega
              rw [Nat.mul_sub]; omega
            rw [this]; exact hb)
          have h2 : lo + n / 2 + (i - n / 2) = lo + i := by omega
          rwa [h2] at h1

end Cayley.Pack

end
