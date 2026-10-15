module

public import Cayley.Soundness.PackSound
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Soundness of the packed Bernstein test

`bernGE P m` checks that every quadratic Bernstein coefficient of the packed polynomial `P`
(layout `L3`) is at least `m`. On `[-1,1]⁵` such a polynomial is a convex combination of its
Bernstein coefficients, so it is at least `m` there.
-/

namespace Cayley.Pack

set_option exponentiation.threshold 1024

open Cayley.K

/-! ## Digits of layout `L3` -/

/-- Digit `i` of slot `j`. -/
def dg (i j : ℕ) : ℕ := j / 3 ^ i % 3

theorem dg_lt (i j : ℕ) : dg i j < 3 := Nat.mod_lt _ (by norm_num)

/-- Shifting a slot whose digit `i` is `0` by `e·3ⁱ` makes that digit `e` and keeps the others. -/
theorem dg_shiftA : ∀ i < 5, ∀ e < 3, ∀ j < 243, dg i j ≠ 0 ∨ j + e * 3 ^ i < 243 := by
  decide +kernel
theorem dg_shiftB : ∀ i < 5, ∀ e < 3, ∀ j < 243, dg i j ≠ 0 ∨ dg i (j + e * 3 ^ i) = e := by
  decide +kernel
set_option synthInstance.maxSize 4096 in
theorem dg_shiftC : ∀ i < 5, ∀ e < 3, ∀ j < 243, ∀ a < 5,
    dg i j ≠ 0 ∨ a = i ∨ dg a (j + e * 3 ^ i) = dg a j := by
  decide +kernel

theorem dg_shift : ∀ i < 5, ∀ e < 3, ∀ j < 243, dg i j = 0 →
    j + e * 3 ^ i < 243 ∧ dg i (j + e * 3 ^ i) = e ∧
      ∀ a < 5, a ≠ i → dg a (j + e * 3 ^ i) = dg a j := by
  intro i hi e he j hj h0
  exact ⟨(dg_shiftA i hi e he j hj).resolve_left (not_not.2 h0),
    (dg_shiftB i hi e he j hj).resolve_left (not_not.2 h0),
    fun a ha hne => ((dg_shiftC i hi e he j hj a ha).resolve_left (not_not.2 h0)).resolve_left hne⟩

theorem dg_unshift0 : ∀ i < 5, ∀ e < 3, ∀ j < 243, dg i j ≠ e ∨
    (e * 3 ^ i ≤ j ∧ dg i (j - e * 3 ^ i) = 0) := by
  decide +kernel

theorem dg_unshift : ∀ i < 5, ∀ e < 3, ∀ j < 243, dg i j = e →
    e * 3 ^ i ≤ j ∧ dg i (j - e * 3 ^ i) = 0 := by
  intro i hi e he j hj h0
  exact (dg_unshift0 i hi e he j hj).resolve_left (not_not.2 h0)

/-- The slots with digit `i` equal to `e` are those with digit `0`, shifted. -/
theorem sum_fiber {M : Type*} [AddCommMonoid M] {i e : ℕ} (hi : i < 5) (he : e < 3) (g : ℕ → M) :
    ∑ j ∈ Finset.range 243, (if dg i j = e then g j else 0) =
      ∑ j ∈ Finset.range 243, (if dg i j = 0 then g (j + e * 3 ^ i) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun j => j + e * 3 ^ i) (fun j => j - e * 3 ^ i)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨h1, h2, -⟩ := dg_shift i hi e he j hj.1 hj.2
    exact ⟨h1, h2⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨h1, h2⟩ := dg_unshift i hi e he j hj.1 hj.2
    exact ⟨by omega, h2⟩
  · intro j _; simp
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    have := (dg_unshift i hi e he j hj.1 hj.2).1
    omega
  · intro j _; rfl

/-- A sum over the slots, grouped along digit `i`. -/
theorem sum_split {M : Type*} [AddCommMonoid M] {i : ℕ} (hi : i < 5) (g : ℕ → M) :
    ∑ j ∈ Finset.range 243, g j = ∑ j ∈ Finset.range 243,
      (if dg i j = 0 then g j + g (j + 3 ^ i) + g (j + 2 * 3 ^ i) else 0) := by
  have h : ∀ j, g j = ((if dg i j = 0 then g j else 0) + (if dg i j = 1 then g j else 0)) +
      (if dg i j = 2 then g j else 0) := by
    intro j
    rcases (by have := dg_lt i j; omega : dg i j = 0 ∨ dg i j = 1 ∨ dg i j = 2) with h | h | h <;>
      simp [h]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_fiber hi (by norm_num : 1 < 3), sum_fiber hi (by norm_num : 2 < 3),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-! ## The coefficient transform -/

/-- The Bernstein matrix on `[-1,1]`: row `κ` (Bernstein index), column `e` (power). -/
def bM : ℕ → ℕ → ℤ
  | 0, 1 => -1
  | 1, 1 => 0
  | 1, 2 => -1
  | _, _ => 1

theorem abs_bM (a b : ℕ) : |bM a b| ≤ 1 := by
  unfold bM; split <;> simp

/-- The Bernstein transform along digit `i` of slot coefficients `c`. -/
def axT (i : ℕ) (c : ℕ → ℤ) (j : ℕ) : ℤ :=
  bM (dg i j) 0 * c (j - dg i j * 3 ^ i) + bM (dg i j) 1 * c (j - dg i j * 3 ^ i + 3 ^ i) +
    bM (dg i j) 2 * c (j - dg i j * 3 ^ i + 2 * 3 ^ i)

theorem axT_shift {i e j : ℕ} (hi : i < 5) (he : e < 3) (hj : j < 243) (h0 : dg i j = 0)
    (c : ℕ → ℤ) :
    axT i c (j + e * 3 ^ i) = bM e 0 * c j + bM e 1 * c (j + 3 ^ i) + bM e 2 * c (j + 2 * 3 ^ i) := by
  obtain ⟨-, h2, -⟩ := dg_shift i hi e he j hj h0
  simp only [axT, h2, Nat.add_sub_cancel]

/-- All five axes. -/
def bT (c : ℕ → ℤ) : ℕ → ℤ := axT 4 (axT 3 (axT 2 (axT 1 (axT 0 c))))

theorem axT_bound {i : ℕ} (hi : i < 5) {c : ℕ → ℤ} {B : ℤ} (hc : ∀ j < 243, |c j| ≤ B) :
    ∀ j < 243, |axT i c j| ≤ 3 * B := by
  intro j hj
  obtain ⟨h1, h2⟩ := dg_unshift i hi _ (dg_lt i j) j hj rfl
  have hj0 : j - dg i j * 3 ^ i < 243 := by omega
  have s1 := (dg_shift i hi 1 (by norm_num) _ hj0 h2).1
  have s2 := (dg_shift i hi 2 (by norm_num) _ hj0 h2).1
  simp only [one_mul] at s1
  have b0 := hc _ hj0; have b1 := hc _ s1; have b2 := hc _ s2
  have m0 := abs_bM (dg i j) 0; have m1 := abs_bM (dg i j) 1; have m2 := abs_bM (dg i j) 2
  unfold axT
  calc _ ≤ |bM (dg i j) 0 * c (j - dg i j * 3 ^ i)| + |bM (dg i j) 1 * c (j - dg i j * 3 ^ i + 3 ^ i)| +
        |bM (dg i j) 2 * c (j - dg i j * 3 ^ i + 2 * 3 ^ i)| := abs_add_three _ _ _
    _ ≤ 1 * B + 1 * B + 1 * B := by
        rw [abs_mul, abs_mul, abs_mul]
        gcongr
    _ = 3 * B := by ring

/-! ## The packed value -/

theorem int_add (a b : ℤ) : Int.add a b = a + b := rfl
theorem int_sub (a b : ℤ) : Int.sub a b = a - b := rfl
theorem int_mul (a b : ℤ) : Int.mul a b = a * b := rfl

/-- The packed integer with slot coefficients `c`. -/
def pv (c : ℕ → ℤ) : ℤ := ∑ j ∈ Finset.range 243, c j * 2 ^ (PW * j)

theorem onesL3_n : onesL3 = packN PW (fun _ => 1) 243 := onesL3_eq

theorem enc_pv {c : ℕ → ℤ} (hc : ∀ j < 243, |c j| < O) :
    Int.toNat (pv c + ((Nat.mul (2 ^ (PW - 1)) onesL3 : ℕ) : ℤ)) = packN PW (odig c) 243 := by
  have hsum : pv c + ((2 ^ (PW - 1) * onesL3 : ℕ) : ℤ) = ((packN PW (odig c) 243 : ℕ) : ℤ) := by
    rw [onesL3_n, pv, packN_eq_sum, packN_eq_sum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := abs_lt.1 (hc j (Finset.mem_range.1 hj))
    have hO : ((2 : ℤ) ^ (PW - 1)) = (O : ℤ) := by simp only [O, Nat.cast_pow, Nat.cast_ofNat]
    rw [odig, Int.toNat_of_nonneg (by omega), hO]
    ring
  rw [nat_mul, hsum, Int.toNat_natCast]

/-! ## Decoding one axis -/

theorem zL3_eq : ∀ i < 5, zL3 i = packN PW (fun j => if dg i j = 0 then 1 else 0) 243 := by
  decide +kernel

theorem land_ite {W n : ℕ} {d : ℕ → ℕ} (hd : ∀ j < n, d j < 2 ^ W) (q : ℕ → Prop)
    [DecidablePred q] :
    packN W d n &&& packN W (fun j => if q j then 2 ^ W - 1 else 0) n =
      packN W (fun j => if q j then d j else 0) n := by
  have h := land_mask hd (m := fun j => if q j then 1 else 0)
    (fun j _ => by split_ifs <;> simp)
  have hm : packN W (fun j => if q j then 2 ^ W - 1 else 0) n =
      packN W (fun j => (2 ^ W - 1) * (if q j then 1 else 0)) n :=
    packN_congr fun j _ => by split_ifs <;> simp
  rw [hm, h]
  exact packN_congr fun j _ => by split_ifs <;> simp

theorem nat_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

/-- Shifting the digit-`0` slots by `e·3ⁱ`. -/
theorem packN_shift {i e : ℕ} (hi : i < 5) (he : e < 3) (x : ℕ → ℕ) :
    packN PW (fun j => if dg i j = e then x j else 0) 243 =
      2 ^ (PW * (e * 3 ^ i)) * packN PW (fun j => if dg i j = 0 then x (j + e * 3 ^ i) else 0) 243 := by
  rw [packN_eq_sum, packN_eq_sum, Finset.mul_sum]
  have h := sum_fiber hi he (fun j => x j * 2 ^ (PW * j))
  simp only [ite_mul, zero_mul] at h ⊢
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [mul_add, pow_add]; ring
  · simp

theorem odig_shift {i e : ℕ} (hi : i < 5) (he : e < 3) {c : ℕ → ℤ} (hc : ∀ j < 243, |c j| < O) :
    ((packN PW (fun j => if dg i j = 0 then odig c (j + e * 3 ^ i) else 0) 243 : ℕ) : ℤ) -
        ((Nat.mul (2 ^ (PW - 1)) (zL3 i) : ℕ) : ℤ) =
      ∑ j ∈ Finset.range 243, (if dg i j = 0 then c (j + e * 3 ^ i) else 0) * 2 ^ (PW * j) := by
  rw [nat_mul, zL3_eq i hi, packN_eq_sum, packN_eq_sum]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hO : ((2 : ℤ) ^ (PW - 1)) = (O : ℤ) := by simp only [O, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs with h0
  · have hj' := abs_lt.1 (hc _ (dg_shift i hi e he j (Finset.mem_range.1 hj) h0).1)
    rw [odig, Int.toNat_of_nonneg (by omega), hO]
    ring
  · simp

theorem shiftRight_part {i e : ℕ} (hi : i < 5) (he : e < 3) {c : ℕ → ℤ} (hc : ∀ j < 243, |c j| < O)
    (s : ℕ) (hs : s = PW * (e * 3 ^ i)) :
    Nat.shiftRight (Nat.land (packN PW (odig c) 243) (Nat.shiftLeft (Nat.mul pM (zL3 i)) s)) s =
      packN PW (fun j => if dg i j = 0 then odig c (j + e * 3 ^ i) else 0) 243 := by
  have hd := odig_lt hc
  have hm : Nat.shiftLeft (Nat.mul pM (zL3 i)) s =
      packN PW (fun j => if dg i j = e then 2 ^ PW - 1 else 0) 243 := by
    rw [nat_shiftLeft, Nat.shiftLeft_eq, nat_mul, zL3_eq i hi, packN_mul_left, pM_eq, hs,
      packN_shift hi he (fun _ => 2 ^ PW - 1), mul_comm]
    exact congrArg (2 ^ (PW * (e * 3 ^ i)) * ·) (packN_congr fun j _ => by split_ifs <;> simp)
  rw [nat_land, hm, land_ite hd, packN_shift hi he, nat_shiftRight, Nat.shiftRight_eq_div_pow,
    hs, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-- **One axis.** `baxis` applies the Bernstein transform along digit `i`. -/
theorem baxis_pv {i : ℕ} (hi : i < 5) {c : ℕ → ℤ} (hc : ∀ j < 243, |c j| < O) :
    baxis i (pv c) = pv (axT i c) := by
  have hN := enc_pv hc
  have p0 : Nat.land (packN PW (odig c) 243) (Nat.mul pM (zL3 i)) =
      packN PW (fun j => if dg i j = 0 then odig c (j + 0 * 3 ^ i) else 0) 243 := by
    have := shiftRight_part hi (by norm_num : 0 < 3) hc 0 (by simp)
    rw [nat_shiftLeft, Nat.shiftLeft_zero, nat_shiftRight, Nat.shiftRight_zero] at this
    exact this
  have p1 := shiftRight_part hi (by norm_num : 1 < 3) hc (Nat.mul PW (3 ^ i)) (by rw [nat_mul, one_mul])
  have p2 := shiftRight_part hi (by norm_num : 2 < 3) hc (Nat.add (Nat.mul PW (3 ^ i)) (Nat.mul PW (3 ^ i)))
    (by rw [nat_add, nat_mul]; ring)
  have q0 := odig_shift hi (by norm_num : 0 < 3) hc
  have q1 := odig_shift hi (by norm_num : 1 < 3) hc
  have q2 := odig_shift hi (by norm_num : 2 < 3) hc
  unfold baxis
  simp only [int_add, int_sub, int_mul, Int.subNatNat_eq_coe]
  rw [hN, p0, p1, p2, q0, q1, q2]
  -- the target, grouped along digit `i`
  conv_rhs => rw [pv, sum_split hi (fun j => axT i c j * 2 ^ (PW * j))]
  have hsh : ((2 ^ Nat.mul PW (3 ^ i) : ℕ) : ℤ) = 2 ^ (PW * 3 ^ i) := by push_cast; rfl
  have hsh2 : ((2 ^ Nat.add (Nat.mul PW (3 ^ i)) (Nat.mul PW (3 ^ i)) : ℕ) : ℤ) =
      2 ^ (PW * 3 ^ i) * 2 ^ (PW * 3 ^ i) := by push_cast; rw [nat_add, nat_mul, pow_add]
  rw [hsh, hsh2]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  split_ifs with h0
  · have a0 := axT_shift hi (by norm_num : 0 < 3) hj' h0 c
    have a1 := axT_shift hi (by norm_num : 1 < 3) hj' h0 c
    have a2 := axT_shift hi (by norm_num : 2 < 3) hj' h0 c
    simp only [zero_mul, add_zero, one_mul] at a0 a1 a2 ⊢
    rw [a0, a1, a2]
    simp only [bM]
    rw [mul_add PW j, mul_add PW j, pow_add, pow_add,
      show PW * (2 * 3 ^ i) = PW * 3 ^ i + PW * 3 ^ i by ring, pow_add]
    ring
  · simp

/-! ## All axes and the sign test -/

theorem bern3_pv {c : ℕ → ℤ} {B : ℤ} (hc : ∀ j < 243, |c j| ≤ B) (hB : 243 * B < O) :
    bern3 (pv c) = pv (bT c) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hc 0 (by norm_num))
  have c1 := axT_bound (by norm_num : 0 < 5) hc
  have c2 := axT_bound (by norm_num : 1 < 5) c1
  have c3 := axT_bound (by norm_num : 2 < 5) c2
  have c4 := axT_bound (by norm_num : 3 < 5) c3
  have lt : ∀ {k : ℤ} {f : ℕ → ℤ}, (∀ j < 243, |f j| ≤ k) → k ≤ 243 * B → ∀ j < 243, |f j| < O :=
    fun h hk j hj => by have := h j hj; omega
  unfold bern3 bT
  rw [baxis_pv (by norm_num) (lt hc (by omega)), baxis_pv (by norm_num) (lt c1 (by omega)),
    baxis_pv (by norm_num) (lt c2 (by omega)), baxis_pv (by norm_num) (lt c3 (by omega)),
    baxis_pv (by norm_num) (lt c4 (by omega))]

theorem bT_bound {c : ℕ → ℤ} {B : ℤ} (hc : ∀ j < 243, |c j| ≤ B) : ∀ j < 243, |bT c j| ≤ 243 * B := by
  have c1 := axT_bound (by norm_num : 0 < 5) hc
  have c2 := axT_bound (by norm_num : 1 < 5) c1
  have c3 := axT_bound (by norm_num : 2 < 5) c2
  have c4 := axT_bound (by norm_num : 3 < 5) c3
  have c5 := axT_bound (by norm_num : 4 < 5) c4
  intro j hj
  have := c5 j hj
  unfold bT
  linarith

theorem packN_inj {W n : ℕ} {d e : ℕ → ℕ} (hd : ∀ j < n, d j < 2 ^ W) (he : ∀ j < n, e j < 2 ^ W)
    (h : packN W d n = packN W e n) : ∀ j < n, d j = e j := by
  intro j hj
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < W
  · have h1 := congrArg (fun x => x.testBit (W * j + k)) h
    simp only [testBit_packN hd, testBit_packN he] at h1
    have hlt : W * j + k < W * n := by
      have : W * (j + 1) ≤ W * n := Nat.mul_le_mul_left _ hj
      rw [Nat.mul_succ] at this; omega
    have hdiv : (W * j + k) / W = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hk, zero_add]
    have hmod : (W * j + k) % W = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    simpa [hlt, hdiv, hmod] using h1
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hd j hj) (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (he j hj) (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem ones_sum : ((onesL3 : ℕ) : ℤ) = ∑ j ∈ Finset.range 243, (2 : ℤ) ^ (PW * j) := by
  rw [onesL3_n, packN_eq_sum]; push_cast; simp

/-- **The sign test.** A passing `bernGE` bounds every Bernstein coefficient from below. -/
theorem bernGE_spec {c : ℕ → ℤ} {B m : ℤ} (hc : ∀ j < 243, |c j| ≤ B) (hB : 243 * B + 2 ^ 390 ≤ O)
    (h : bernGE (pv c) m = true) : ∀ j < 243, m ≤ bT c j := by
  unfold bernGE at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hm, hs⟩ := h
  have hm' : |m| < 2 ^ 390 := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hm
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hc 0 (by norm_num))
  have hb := bT_bound hc
  have hc' : ∀ j < 243, |(fun j => bT c j - m) j| < O := by
    intro j hj
    have := hb j hj
    calc _ ≤ |bT c j| + |m| := abs_sub _ _
      _ < O := by linarith
  have hpv : bern3 (pv c) - (onesL3 : ℤ) * m = pv (fun j => bT c j - m) := by
    have h390 : (0 : ℤ) < 2 ^ 390 := by positivity
    rw [bern3_pv hc (lt_of_lt_of_le (lt_add_of_pos_right _ h390) hB), pv, pv, ones_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have he := enc_pv hc'
  rw [int_add, int_sub, int_mul, hpv] at hs
  simp only [he] at hs
  rw [nat_land, nat_shiftRight, onesL3_n, packN_signs PW_pos (odig_lt hc')] at hs
  have hd1 : ∀ j < 243, odig (fun j => bT c j - m) j / 2 ^ (PW - 1) < 2 ^ PW := fun j hj =>
    lt_of_le_of_lt (Nat.div_le_self _ _) (odig_lt hc' j hj)
  have hi := packN_inj hd1 (fun _ _ => Nat.one_lt_two_pow (by decide)) hs
  intro j hj
  have := hi j hj
  have hO : (2 : ℕ) ^ (PW - 1) = O := rfl
  rw [odig, hO, odig_div (hc' j hj)] at this
  split_ifs at this with h0
  · simpa using h0

/-! ## The polynomial is a convex combination of its Bernstein coefficients -/

/-- The quadratic Bernstein basis on `[-1,1]`. -/
noncomputable def bβ (κ : ℕ) (x : ℝ) : ℝ :=
  if κ = 0 then ((1 - x) / 2) ^ 2 else if κ = 1 then (1 - x ^ 2) / 2 else ((1 + x) / 2) ^ 2

theorem bβ_nonneg (κ : ℕ) {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ bβ κ x := by
  unfold bβ
  have : x ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
  split_ifs <;> positivity

theorem bβ_sum (x : ℝ) {e : ℕ} (he : e < 3) :
    (bM 0 e : ℝ) * bβ 0 x + bM 1 e * bβ 1 x + bM 2 e * bβ 2 x = x ^ e := by
  interval_cases e <;> simp [bM, bβ] <;> ring

theorem axis_real {i : ℕ} (hi : i < 5) (c : ℕ → ℤ) (φ : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ e < 3, (bM 0 e : ℝ) * g 0 + bM 1 e * g 1 + bM 2 e * g 2 = φ i e) :
    ∑ j ∈ Finset.range 243, (axT i c j : ℝ) * ∏ a ∈ Finset.range 5, Function.update φ i g a (dg a j) =
      ∑ j ∈ Finset.range 243, (c j : ℝ) * ∏ a ∈ Finset.range 5, φ a (dg a j) := by
  have hmem : i ∈ Finset.range 5 := Finset.mem_range.2 hi
  set R : ℕ → ℝ := fun j => ∏ a ∈ (Finset.range 5).erase i, φ a (dg a j) with hRdef
  have hL : ∀ j, ∏ a ∈ Finset.range 5, Function.update φ i g a (dg a j) = g (dg i j) * R j := by
    intro j
    rw [← Finset.mul_prod_erase _ _ hmem, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun a ha => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
  have hR : ∀ j, ∏ a ∈ Finset.range 5, φ a (dg a j) = φ i (dg i j) * R j := fun j =>
    (Finset.mul_prod_erase _ _ hmem).symm
  have hRs : ∀ e < 3, ∀ j < 243, dg i j = 0 → R (j + e * 3 ^ i) = R j := by
    intro e he j hj h0
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [(dg_shift i hi e he j hj h0).2.2 a (Finset.mem_range.1 (Finset.mem_of_mem_erase ha))
      (Finset.ne_of_mem_erase ha)]
  simp only [hL, hR]
  conv_lhs => rw [sum_split hi]
  conv_rhs => rw [sum_split hi]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  split_ifs with h0
  · have a0 := axT_shift hi (by norm_num : 0 < 3) hj' h0 c
    have a1 := axT_shift hi (by norm_num : 1 < 3) hj' h0 c
    have a2 := axT_shift hi (by norm_num : 2 < 3) hj' h0 c
    have d1 := (dg_shift i hi 1 (by norm_num) j hj' h0).2.1
    have d2 := (dg_shift i hi 2 (by norm_num) j hj' h0).2.1
    have r1 := hRs 1 (by norm_num) j hj' h0
    have r2 := hRs 2 (by norm_num) j hj' h0
    simp only [zero_mul, add_zero, one_mul] at a0 a1 a2 d1 d2 r1 r2
    rw [a0, a1, a2, d1, d2, r1, r2, h0, ← hg 0 (by norm_num), ← hg 1 (by norm_num),
      ← hg 2 (by norm_num)]
    push_cast
    ring
  · rfl

/-- The weights after converting the first `k` axes. -/
noncomputable def φk (t : ℕ → ℝ) (k : ℕ) (a d : ℕ) : ℝ := if a < k then bβ d (t a) else t a ^ d

theorem φk_succ (t : ℕ → ℝ) (k : ℕ) :
    Function.update (φk t k) k (fun d => bβ d (t k)) = φk t (k + 1) := by
  funext a d
  by_cases ha : a = k
  · subst ha; simp [φk]
  · rw [Function.update_of_ne ha]
    simp only [φk]
    have : a < k ↔ a < k + 1 := by omega
    simp only [this]

theorem bern_real (c : ℕ → ℤ) (t : ℕ → ℝ) :
    ∑ j ∈ Finset.range 243, (bT c j : ℝ) * ∏ a ∈ Finset.range 5, bβ (dg a j) (t a) =
      ∑ j ∈ Finset.range 243, (c j : ℝ) * ∏ a ∈ Finset.range 5, t a ^ dg a j := by
  have step : ∀ k < 5, ∀ c : ℕ → ℤ,
      ∑ j ∈ Finset.range 243, (axT k c j : ℝ) * ∏ a ∈ Finset.range 5, φk t (k + 1) a (dg a j) =
        ∑ j ∈ Finset.range 243, (c j : ℝ) * ∏ a ∈ Finset.range 5, φk t k a (dg a j) := by
    intro k hk c
    rw [← φk_succ]
    apply axis_real hk
    intro e he
    simp only [φk, lt_irrefl, ite_false]
    exact bβ_sum (t k) he
  have e5 : ∀ j, ∏ a ∈ Finset.range 5, bβ (dg a j) (t a) = ∏ a ∈ Finset.range 5, φk t 5 a (dg a j) :=
    fun j => Finset.prod_congr rfl fun a ha => by simp [φk, Finset.mem_range.1 ha]
  have e0 : ∀ j, ∏ a ∈ Finset.range 5, t a ^ dg a j = ∏ a ∈ Finset.range 5, φk t 0 a (dg a j) :=
    fun j => Finset.prod_congr rfl fun a _ => by simp [φk]
  simp only [e5, e0]
  unfold bT
  rw [step 4 (by norm_num), step 3 (by norm_num), step 2 (by norm_num), step 1 (by norm_num),
    step 0 (by norm_num)]

theorem bT_delta : ∀ j < 243, bT (fun j => if j = 0 then 1 else 0) j = 1 := by
  decide +kernel

/-- **Bernstein bound.** A passing `bernGE` bounds the polynomial on `[-1,1]⁵`. -/
theorem bernGE_le {e : PE} (h : L3.Fits e) {m : ℤ} (hb : 243 * (e.nrm : ℤ) + 2 ^ 390 ≤ O)
    (hok : bernGE (e.ev fun i => pX i) m = true) {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) :
    (m : ℝ) ≤ e.ev t := by
  set c := L3.cf e with hcdef
  have hpv : e.ev (fun i => pX i) = pv c := by
    rw [pX_eq]; exact Layout.ev_kron L3_good h PW
  have hc : ∀ j < 243, |c j| ≤ (e.nrm : ℤ) := fun j _ => Layout.abs_cf_le j
  rw [hpv] at hok
  have hm := bernGE_spec hc hb hok
  set tt : ℕ → ℝ := fun a => if h : a < 5 then t ⟨a, h⟩ else 0 with httdef
  have htt : ∀ a, |tt a| ≤ 1 := fun a => by
    simp only [tt]; split_ifs
    · exact ht _
    · simp
  have hev : e.ev t = ∑ j ∈ Finset.range 243, (c j : ℝ) * ∏ a ∈ Finset.range 5, tt a ^ dg a j := by
    rw [Layout.ev_eq_sum L3_good h]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  have hW : ∀ j, 0 ≤ ∏ a ∈ Finset.range 5, bβ (dg a j) (tt a) := fun j =>
    Finset.prod_nonneg fun a _ => bβ_nonneg _ (htt a)
  have hsum : ∑ j ∈ Finset.range 243, ∏ a ∈ Finset.range 5, bβ (dg a j) (tt a) = 1 := by
    have h1 := bern_real (fun j => if j = 0 then 1 else 0) tt
    have hl : ∀ j ∈ Finset.range 243,
        ((bT (fun j => if j = 0 then 1 else 0) j : ℤ) : ℝ) * ∏ a ∈ Finset.range 5, bβ (dg a j) (tt a) =
          ∏ a ∈ Finset.range 5, bβ (dg a j) (tt a) := fun j hj => by
      rw [bT_delta j (Finset.mem_range.1 hj), Int.cast_one, one_mul]
    have hr : ∑ j ∈ Finset.range 243, (((if j = 0 then 1 else 0 : ℤ)) : ℝ) *
        ∏ a ∈ Finset.range 5, tt a ^ dg a j = 1 := by
      rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp)]
      simp [dg]
    rw [Finset.sum_congr rfl hl] at h1
    rw [h1, hr]
  rw [hev, ← bern_real]
  calc (m : ℝ) = ∑ j ∈ Finset.range 243, (m : ℝ) * ∏ a ∈ Finset.range 5, bβ (dg a j) (tt a) := by
        rw [← Finset.mul_sum, hsum, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm j (Finset.mem_range.1 hj)) (hW j)

end Cayley.Pack

end
