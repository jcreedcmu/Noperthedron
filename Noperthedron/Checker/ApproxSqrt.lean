import Mathlib.Data.Real.Sqrt

import Noperthedron.RationalApprox.Basic

/-!
# Rational square-root approximations (§7.2.2 of [SY25])

We define computable upper and lower rational square-root functions,
following Definition 47 and §7.2.2 of SY25.

For all `x : ℚ` with `0 ≤ x`:

  `sqrtℚLow x ≤ √(x : ℝ) ≤ sqrtℚUp x`,

and both functions return `0` on negative input (matching the convention used
by `Real.sqrt`).

## Construction

* `x = 0` ↦ both return `0`.
* `x > 0`: write `x = p/q` (in lowest terms, `p, q > 0`). We find the unique
  integer `a` such that `p · 100^a / q ∈ [10^20, 10^22)`, then compute
    `m := ⌊p · 100^a / q⌋`,
    `b := ⌊√m⌋`,
    `sqrtℚLow x := b · 10^(-a)`,
    `sqrtℚUp  x := 1 / sqrtℚLow (1/x)`.
  This guarantees ten decimal digits of accuracy.

The implementation works in pure ℕ-arithmetic for the scale search, avoiding
the gcd cost of repeated rational multiplication. We maintain a state pair
`(num, den)` with the invariant `num/den = x · 100^a`. An "up" step multiplies
`num` by 100 (incrementing `a`); a "down" step multiplies `den` by 100
(decrementing `a`). Once in the window, `m = num / den` (integer division).
-/

namespace RationalApprox

open scoped BigOperators

/-! ## Constants and search loops -/

private def lo : ℕ := 10 ^ 20
private def hi : ℕ := 10 ^ 22

/-- **Up-search**: starting from `num`, multiply by 100 each step (incrementing
`k`) until either `num ≥ threshold` or fuel is exhausted. Returns `(k, num)`. -/
private def shiftUpAux (threshold : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | num, k, 0          => (k, num)
  | num, k, fuel + 1   =>
      if num ≥ threshold then (k, num)
      else shiftUpAux threshold (num * 100) (k + 1) fuel

/-- **Down-search**: starting from `den`, multiply by 100 each step (incrementing
`k`) until either `numDivHi < den` or fuel is exhausted. Returns `(k, den)`.
The condition `numDivHi < den` is equivalent to `num < hi · den` when
`numDivHi = num / hi` (integer division). -/
private def shiftDownAux (numDivHi : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | den, k, 0          => (k, den)
  | den, k, fuel + 1   =>
      if numDivHi < den then (k, den)
      else shiftDownAux numDivHi (den * 100) (k + 1) fuel

/-! ## The square-root functions -/

/-- Implementation of the lower rational square-root for `x = p/q > 0`,
parametrised by `fuel`. Returns the rational `(b : ℚ) · 10^(-a)` where
`a` is the chosen scale exponent and `b = ⌊√⌊p · 100^a / q⌋⌋`. -/
private def sqrtℚLowImpl (p q fuel : ℕ) : ℚ :=
  if p < lo * q then
    let res := shiftUpAux (lo * q) p 0 fuel
    ((Nat.sqrt (res.2 / q) : ℚ)) * (10 : ℚ) ^ (-(res.1 : ℤ))
  else if p < hi * q then
    ((Nat.sqrt (p / q) : ℚ))
  else
    let res := shiftDownAux (p / hi) q 0 fuel
    ((Nat.sqrt (p / res.2) : ℚ)) * (10 : ℚ) ^ (res.1 : ℤ)

/-- **Lower rational square-root** (`√⁻`): returns `0` on `x ≤ 0`; otherwise
returns a rational `r` with `r ≤ √x`. -/
def sqrtℚLow (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else
    let p : ℕ := x.num.toNat
    let q : ℕ := x.den
    let fuel : ℕ := Nat.log 10 p + Nat.log 10 q + 100
    sqrtℚLowImpl p q fuel

/-- **Upper rational square-root** (`√⁺`): returns `0` on `x ≤ 0`; otherwise
returns a rational `r` with `√x ≤ r`, defined as `1 / √⁻ (1/x)`. -/
def sqrtℚUp (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else 1 / sqrtℚLow (1 / x)

/-! ## Norms induced on rational vectors

The paper uses, for `Z ∈ ℚⁿ`:
  `‖Z‖₊ := √⁺ ‖Z‖²`,  `‖Z‖₋ := √⁻ ‖Z‖²`.
-/

/-- Squared Euclidean norm of a rational vector, taking values in `ℚ`. -/
def normSqℚ {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  ∑ i, v i * v i

/-- Lower-rational Euclidean norm: `‖v‖₋ ≤ ‖v‖`. -/
def normLowℚ {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  sqrtℚLow (normSqℚ v)

/-- Upper-rational Euclidean norm: `‖v‖ ≤ ‖v‖₊`. -/
def normUpℚ {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  sqrtℚUp (normSqℚ v)

/-! ## Search-loop invariants -/

/-- Each step of `shiftUpAux` multiplies `num` by 100 and increments `k` by 1.
Hence the loop output `(k', num')` satisfies `k' = k + s` and `num' = num · 100^s`
for some step count `s ≤ fuel`. -/
private lemma shiftUpAux_invariant (threshold : ℕ) :
    ∀ (num k fuel : ℕ),
      ∃ s : ℕ, s ≤ fuel ∧
        (shiftUpAux threshold num k fuel).1 = k + s ∧
        (shiftUpAux threshold num k fuel).2 = num * 100 ^ s := by
  intro num k fuel
  induction fuel generalizing num k with
  | zero =>
    refine ⟨0, le_refl 0, ?_, ?_⟩ <;> simp [shiftUpAux]
  | succ f ih =>
    by_cases h : num ≥ threshold
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩ <;> simp [shiftUpAux, h]
    · obtain ⟨s, hs_le, hs_k, hs_num⟩ := ih (num := num * 100) (k := k + 1)
      refine ⟨s + 1, Nat.succ_le_succ hs_le, ?_, ?_⟩
      · simp only [shiftUpAux, if_neg h]
        rw [hs_k]; ring
      · simp only [shiftUpAux, if_neg h]
        rw [hs_num, pow_succ]; ring

/-- Each step of `shiftDownAux` multiplies `den` by 100 and increments `k` by 1. -/
private lemma shiftDownAux_invariant (numDivHi : ℕ) :
    ∀ (den k fuel : ℕ),
      ∃ s : ℕ, s ≤ fuel ∧
        (shiftDownAux numDivHi den k fuel).1 = k + s ∧
        (shiftDownAux numDivHi den k fuel).2 = den * 100 ^ s := by
  intro den k fuel
  induction fuel generalizing den k with
  | zero =>
    refine ⟨0, le_refl 0, ?_, ?_⟩ <;> simp [shiftDownAux]
  | succ f ih =>
    by_cases h : numDivHi < den
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩ <;> simp [shiftDownAux, h]
    · obtain ⟨s, hs_le, hs_k, hs_den⟩ := ih (den := den * 100) (k := k + 1)
      refine ⟨s + 1, Nat.succ_le_succ hs_le, ?_, ?_⟩
      · simp only [shiftDownAux, if_neg h]
        rw [hs_k]; ring
      · simp only [shiftDownAux, if_neg h]
        rw [hs_den, pow_succ]; ring

/-- Up-search termination: if the available fuel is enough to amplify `num` past
`threshold`, then the result satisfies `num' ≥ threshold`. -/
private lemma shiftUpAux_terminates (threshold : ℕ) :
    ∀ (num k fuel : ℕ), threshold ≤ num * 100 ^ fuel →
      threshold ≤ (shiftUpAux threshold num k fuel).2 := by
  intro num k fuel
  induction fuel generalizing num k with
  | zero =>
    intro h
    simp only [shiftUpAux]
    simpa using h
  | succ f ih =>
    intro h
    by_cases hnum : num ≥ threshold
    · simp [shiftUpAux, hnum]
    · simp only [shiftUpAux, if_neg hnum]
      apply ih
      have hrw : num * 100 ^ (f + 1) = num * 100 * 100 ^ f := by
        rw [pow_succ]; ring
      rw [hrw] at h; exact h

/-- Down-search termination: if the available fuel is enough to amplify `den` past
`numDivHi`, then the result satisfies `numDivHi < den'`. -/
private lemma shiftDownAux_terminates (numDivHi : ℕ) :
    ∀ (den k fuel : ℕ), numDivHi < den * 100 ^ fuel →
      numDivHi < (shiftDownAux numDivHi den k fuel).2 := by
  intro den k fuel
  induction fuel generalizing den k with
  | zero =>
    intro h
    simp only [shiftDownAux]
    simpa using h
  | succ f ih =>
    intro h
    by_cases hd : numDivHi < den
    · simp [shiftDownAux, hd]
    · simp only [shiftDownAux, if_neg hd]
      apply ih
      have hrw : den * 100 ^ (f + 1) = den * 100 * 100 ^ f := by
        rw [pow_succ]; ring
      rw [hrw] at h; exact h

/-- Bound on the down-search result: `den_final ≤ max den₀ (100 · numDivHi)`.
This holds unconditionally — if we never step the result is `den₀`; if we step
the previous value `den_prev` satisfied `den_prev ≤ numDivHi`, so the new
value is `100 · den_prev ≤ 100 · numDivHi`. -/
private lemma shiftDownAux_le_max (numDivHi : ℕ) :
    ∀ (den k fuel : ℕ),
      (shiftDownAux numDivHi den k fuel).2 ≤ max den (100 * numDivHi) := by
  intro den k fuel
  induction fuel generalizing den k with
  | zero =>
    simp only [shiftDownAux]
    exact le_max_left _ _
  | succ f ih =>
    by_cases h : numDivHi < den
    · simp only [shiftDownAux, if_pos h]; exact le_max_left _ _
    · simp only [shiftDownAux, if_neg h]
      push Not at h
      -- h : den ≤ numDivHi
      have hih := ih (den := den * 100) (k := k + 1)
      -- den * 100 ≤ 100 * numDivHi (commute & multiply)
      have h_step : den * 100 ≤ 100 * numDivHi := by
        rw [mul_comm den 100]; exact Nat.mul_le_mul_left _ h
      calc (shiftDownAux numDivHi (den * 100) (k + 1) f).2
          ≤ max (den * 100) (100 * numDivHi) := hih
        _ ≤ 100 * numDivHi := max_le h_step (le_refl _)
        _ ≤ max den (100 * numDivHi) := le_max_right _ _

/-! ## Basic non-negativity -/

private lemma sqrtℚLowImpl_nonneg (p q fuel : ℕ) : 0 ≤ sqrtℚLowImpl p q fuel := by
  unfold sqrtℚLowImpl
  split_ifs <;> first | rfl | positivity

theorem sqrtℚLow_nonneg (x : ℚ) : 0 ≤ sqrtℚLow x := by
  unfold sqrtℚLow
  split_ifs with h
  · exact le_refl 0
  · exact sqrtℚLowImpl_nonneg _ _ _

theorem sqrtℚUp_nonneg (x : ℚ) : 0 ≤ sqrtℚUp x := by
  unfold sqrtℚUp
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg zero_le_one (sqrtℚLow_nonneg _)

/-! ## Squared lower bound and positivity

The bound `(sqrtℚLow x)^2 ≤ x` follows uniformly from a single algebraic fact:
in each branch we maintain a positive `(num, den) : ℕ × ℕ` with
`(num : ℝ) / den = (x : ℝ) * 100^a`, and set `b = ⌊√⌊num/den⌋⌋`. Then
`(b : ℝ)^2 ≤ (num : ℝ) / den = x · 100^a`, from which
`((b : ℝ) · 10^(-a))^2 ≤ x` follows by multiplying by `100^(-a)`. -/

private lemma rat_pos_eq (x : ℚ) (hx : 0 < x) :
    ((x.num.toNat : ℕ) : ℝ) / ((x.den : ℕ) : ℝ) = (x : ℝ) := by
  have hnum_pos : 0 < x.num := Rat.num_pos.mpr hx
  have hcast : ((x.num.toNat : ℕ) : ℝ) = (x.num : ℝ) := by
    have : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg (le_of_lt hnum_pos)
    exact_mod_cast this
  rw [hcast]
  rw [show (x : ℝ) = ((x.num : ℝ) / (x.den : ℝ)) from by
        push_cast [Rat.cast_def]; rfl]

/-- Core algebraic fact: from `b² · den ≤ num` (in ℕ) and `(num : ℝ) = xR · 100^a · den`,
deduce `(b · 10^(-a))² ≤ xR` in ℝ. -/
private lemma sq_bound_aux (xR : ℝ) (a : ℤ) (numN denN b : ℕ)
    (hden : 0 < denN)
    (hscaled : (numN : ℝ) = xR * (100 : ℝ) ^ a * (denN : ℝ))
    (hb : b * b * denN ≤ numN) :
    ((b : ℝ) * (10 : ℝ) ^ (-a)) ^ 2 ≤ xR := by
  have hdenR : (0 : ℝ) < (denN : ℝ) := by exact_mod_cast hden
  have hbR : (b : ℝ) * b * (denN : ℝ) ≤ (numN : ℝ) := by exact_mod_cast hb
  -- numN = xR · 100^a · denN, so divide by denN > 0
  have hbR' : (b : ℝ) * b ≤ xR * (100 : ℝ) ^ a := by
    rw [hscaled] at hbR
    have hdenR_ne : (denN : ℝ) ≠ 0 := ne_of_gt hdenR
    calc (b : ℝ) * b
        = (b : ℝ) * b * (denN : ℝ) * (denN : ℝ)⁻¹ := by field_simp
      _ ≤ xR * (100 : ℝ) ^ a * (denN : ℝ) * (denN : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hbR (le_of_lt (inv_pos.mpr hdenR))
      _ = xR * (100 : ℝ) ^ a := by field_simp
  -- ((b) * 10^(-a))² = b² * 100^(-a)
  have hLHS : ((b : ℝ) * (10 : ℝ) ^ (-a)) ^ 2 = (b : ℝ) * b * (100 : ℝ) ^ (-a) := by
    have h10sq : ((10 : ℝ) ^ (-a)) ^ 2 = (100 : ℝ) ^ (-a) := by
      rw [show ((10 : ℝ) ^ (-a)) ^ 2 = (10 : ℝ) ^ (2 * -a) from by
        rw [show (2 * -a : ℤ) = -a + -a from by ring,
            zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0), pow_two]]
      rw [show (100 : ℝ) = 10 ^ 2 from by norm_num]
      rw [← zpow_natCast (10 : ℝ) 2, ← zpow_mul]
      ring_nf
    rw [mul_pow, pow_two (b : ℝ), h10sq]
  rw [hLHS]
  -- b² * 100^(-a) ≤ xR
  have h100neg_pos : (0 : ℝ) < (100 : ℝ) ^ (-a) := zpow_pos (by norm_num) _
  calc (b : ℝ) * b * (100 : ℝ) ^ (-a)
      ≤ xR * (100 : ℝ) ^ a * (100 : ℝ) ^ (-a) :=
        mul_le_mul_of_nonneg_right hbR' (le_of_lt h100neg_pos)
    _ = xR := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (100 : ℝ) ≠ 0)]; simp

/-- Squared lower bound for the implementation: if `xR = (p : ℝ)/q` with `q > 0`,
then `(sqrtℚLowImpl p q fuel)² ≤ xR`. -/
private lemma sqrtℚLowImpl_sq_le (p q fuel : ℕ) (hq : 0 < q) :
    ((sqrtℚLowImpl p q fuel : ℚ) : ℝ) ^ 2 ≤ ((p : ℝ) / q) := by
  unfold sqrtℚLowImpl
  split_ifs with hbr1 hbr2
  · -- Branch 1: p < lo * q (up-search)
    obtain ⟨s, _, hk_eq, hnum_eq⟩ := shiftUpAux_invariant (lo * q) p 0 fuel
    set res := shiftUpAux (lo * q) p 0 fuel
    have hk : res.1 = s := by simp [hk_eq]
    have hnum : res.2 = p * 100 ^ s := by simp [hnum_eq]
    have hcast :
        (((Nat.sqrt (res.2 / q) : ℚ) * (10 : ℚ) ^ (-(res.1 : ℤ)) : ℚ) : ℝ)
        = ((Nat.sqrt (res.2 / q) : ℝ)) * (10 : ℝ) ^ (-(res.1 : ℤ)) := by
      push_cast; rfl
    rw [hcast]
    apply sq_bound_aux ((p : ℝ) / q) (res.1 : ℤ) res.2 q (Nat.sqrt (res.2 / q)) hq
    · -- (res.2 : ℝ) = (p/q) · 100^res.1 · q
      rw [hnum, hk]
      push_cast
      rw [zpow_natCast]
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq)
      field_simp
    · calc Nat.sqrt (res.2 / q) * Nat.sqrt (res.2 / q) * q
          ≤ (res.2 / q) * q := Nat.mul_le_mul_right _ (Nat.sqrt_le _)
        _ ≤ res.2 := Nat.div_mul_le_self _ _
  · -- Branch 2: lo*q ≤ p < hi*q (a = 0)
    have hcast : ((Nat.sqrt (p / q) : ℚ) : ℝ) = (Nat.sqrt (p / q) : ℝ) := by push_cast; rfl
    rw [hcast]
    rw [show ((Nat.sqrt (p / q) : ℝ))
        = ((Nat.sqrt (p / q) : ℝ)) * (10 : ℝ) ^ (-(0 : ℤ)) from by simp]
    apply sq_bound_aux ((p : ℝ) / q) (0 : ℤ) p q (Nat.sqrt (p / q)) hq
    · have hqne : (q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq)
      field_simp
    · calc Nat.sqrt (p / q) * Nat.sqrt (p / q) * q
          ≤ (p / q) * q := Nat.mul_le_mul_right _ (Nat.sqrt_le _)
        _ ≤ p := Nat.div_mul_le_self _ _
  · -- Branch 3: p ≥ hi * q (down-search; a = -k)
    obtain ⟨s, _, hk_eq, hden_eq⟩ := shiftDownAux_invariant (p / hi) q 0 fuel
    set res := shiftDownAux (p / hi) q 0 fuel
    have hk : res.1 = s := by simp [hk_eq]
    have hden : res.2 = q * 100 ^ s := by simp [hden_eq]
    have hden_pos : 0 < res.2 := by rw [hden]; positivity
    have hcast :
        (((Nat.sqrt (p / res.2) : ℚ) * (10 : ℚ) ^ (res.1 : ℤ) : ℚ) : ℝ)
        = ((Nat.sqrt (p / res.2) : ℝ)) * (10 : ℝ) ^ (-(-(res.1 : ℤ))) := by
      push_cast; rw [neg_neg]
    rw [hcast]
    apply sq_bound_aux ((p : ℝ) / q) (-(res.1 : ℤ)) p res.2 (Nat.sqrt (p / res.2)) hden_pos
    · rw [hden, hk]
      push_cast
      rw [zpow_neg, zpow_natCast]
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq)
      have h100ne : (100 : ℝ) ≠ 0 := by norm_num
      have h100ne' : (100 : ℝ)^s ≠ 0 := pow_ne_zero _ h100ne
      field_simp
    · calc Nat.sqrt (p / res.2) * Nat.sqrt (p / res.2) * res.2
          ≤ (p / res.2) * res.2 := Nat.mul_le_mul_right _ (Nat.sqrt_le _)
        _ ≤ p := Nat.div_mul_le_self _ _

/-- Squared lower bound: `(sqrtℚLow x)^2 ≤ x` (cast to ℝ) for `0 ≤ x`. -/
private lemma sqrtℚLow_sq_le (x : ℚ) (hx : 0 ≤ x) :
    ((sqrtℚLow x : ℚ) : ℝ) ^ 2 ≤ ((x : ℚ) : ℝ) := by
  rw [sqrtℚLow]
  split_ifs with h0
  · -- x ≤ 0 and 0 ≤ x: x = 0
    have : x = 0 := le_antisymm h0 hx
    simp [this]
  · push Not at h0
    have hxpos : 0 < x := h0
    have hq_pos : 0 < x.den := x.pos
    have hxR_eq : ((x.num.toNat : ℕ) : ℝ) / ((x.den : ℕ) : ℝ) = (x : ℝ) :=
      rat_pos_eq x hxpos
    have h := sqrtℚLowImpl_sq_le x.num.toNat x.den
      (Nat.log 10 x.num.toNat + Nat.log 10 x.den + 100) hq_pos
    rw [hxR_eq] at h
    exact h

/-- `√⁻ x ≤ √x` for `x ≥ 0` (Definition 47). -/
theorem sqrtℚLow_le_sqrt {x : ℚ} (hx : 0 ≤ x) :
    ((sqrtℚLow x : ℚ) : ℝ) ≤ Real.sqrt ((x : ℚ) : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  exact sqrtℚLow_sq_le x hx

/-! ### Positivity of `sqrtℚLow` for positive input

The proof uses the fuel-sufficient termination of the search to ensure the
integer floor `m` of `x · 100^a` is at least `lo = 10^20 ≥ 1`. -/

private lemma lo_pos : 1 ≤ lo := by unfold lo; norm_num

private lemma hi_pos : 1 ≤ hi := by unfold hi; norm_num

private lemma hundred_pow_eq (n : ℕ) : (100 : ℕ) ^ n = 10 ^ (2 * n) := by
  rw [show (100 : ℕ) = 10 ^ 2 from rfl, ← pow_mul]

/-- For `p, q > 0`, the implementation is positive provided the fuel exceeds
`Nat.log 10 p + Nat.log 10 q + 100`. -/
private lemma sqrtℚLowImpl_pos (p q fuel : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hfuel : Nat.log 10 p + Nat.log 10 q + 100 ≤ fuel) :
    0 < sqrtℚLowImpl p q fuel := by
  have hp_lt : p < 10 ^ (Nat.log 10 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  have hq_lt : q < 10 ^ (Nat.log 10 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  -- 100^fuel ≥ 10^(N + 1) and 10^(D + 21)
  have h100_ge_p : (10 : ℕ) ^ (Nat.log 10 p + 1) ≤ 100 ^ fuel := by
    rw [hundred_pow_eq]
    apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 10); omega
  have h100_ge_loq : (10 : ℕ) ^ (Nat.log 10 q + 21) ≤ 100 ^ fuel := by
    rw [hundred_pow_eq]
    apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 10); omega
  unfold sqrtℚLowImpl
  split_ifs with hbr1 hbr2
  · -- Up-search branch
    set res := shiftUpAux (lo * q) p 0 fuel
    -- num ≥ lo * q
    have hterm : lo * q ≤ res.2 := by
      apply shiftUpAux_terminates
      have h1 : lo * q ≤ 10 ^ 20 * 10 ^ (Nat.log 10 q + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hq_lt)
      have h2 : (10 : ℕ) ^ 20 * 10 ^ (Nat.log 10 q + 1) = 10 ^ (Nat.log 10 q + 21) := by
        rw [← pow_add]; congr 1; omega
      calc lo * q
          ≤ 10 ^ 20 * 10 ^ (Nat.log 10 q + 1) := h1
        _ = 10 ^ (Nat.log 10 q + 21) := h2
        _ ≤ 100 ^ fuel := h100_ge_loq
        _ ≤ p * 100 ^ fuel := Nat.le_mul_of_pos_left _ hp
    have hnum_ge : lo ≤ res.2 / q := by
      have : (lo * q) / q ≤ res.2 / q := Nat.div_le_div_right hterm
      rwa [Nat.mul_div_cancel _ hq] at this
    have hb_pos : 1 ≤ Nat.sqrt (res.2 / q) :=
      Nat.le_sqrt'.mpr (le_trans lo_pos hnum_ge)
    have hbq_pos : (0 : ℚ) < (Nat.sqrt (res.2 / q) : ℚ) := by exact_mod_cast hb_pos
    have h10z_pos : (0 : ℚ) < (10 : ℚ) ^ (-(res.1 : ℤ)) := zpow_pos (by norm_num) _
    exact mul_pos hbq_pos h10z_pos
  · -- Branch 2: a = 0
    push Not at hbr1
    have hpq_ge : lo ≤ p / q := by
      have : (lo * q) / q ≤ p / q := Nat.div_le_div_right hbr1
      rwa [Nat.mul_div_cancel _ hq] at this
    have hb_pos : 1 ≤ Nat.sqrt (p / q) := Nat.le_sqrt'.mpr (le_trans lo_pos hpq_ge)
    exact_mod_cast hb_pos
  · -- Branch 3: down-search
    push Not at hbr1 hbr2
    -- hbr1 : lo * q ≤ p,  hbr2 : hi * q ≤ p
    set res := shiftDownAux (p / hi) q 0 fuel
    -- Bound res.2: by the unconditional max bound, res.2 ≤ max q (100 * (p/hi)) ≤ p.
    have hres2_le_p : res.2 ≤ p := by
      have hbound : res.2 ≤ max q (100 * (p / hi)) := shiftDownAux_le_max _ _ _ _
      have hq_le_p : q ≤ p := by
        have hi_ge_one : 1 ≤ hi := hi_pos
        calc q = 1 * q := (one_mul q).symm
          _ ≤ hi * q := Nat.mul_le_mul_right _ hi_ge_one
          _ ≤ p := hbr2
      have h100_le_p : 100 * (p / hi) ≤ p := by
        have hhi_ge_100 : 100 ≤ hi := by unfold hi; norm_num
        have : p / hi ≤ p / 100 := Nat.div_le_div_left hhi_ge_100 (by norm_num)
        calc 100 * (p / hi) ≤ 100 * (p / 100) := Nat.mul_le_mul_left _ this
          _ ≤ p := Nat.mul_div_le _ _
      calc res.2 ≤ max q (100 * (p / hi)) := hbound
        _ ≤ p := max_le hq_le_p h100_le_p
    -- res.2 must be positive (it equals q * 100^s for some s)
    obtain ⟨s, _, _, hden_eq⟩ := shiftDownAux_invariant (p / hi) q 0 fuel
    have hres2_pos : 0 < res.2 := by
      have h : res.2 = q * 100 ^ s := hden_eq
      rw [h]; positivity
    -- p / res.2 ≥ 1
    have hpd : 1 ≤ p / res.2 := (Nat.one_le_div_iff hres2_pos).mpr hres2_le_p
    have hb_pos : 1 ≤ Nat.sqrt (p / res.2) := Nat.le_sqrt'.mpr hpd
    have hbq_pos : (0 : ℚ) < (Nat.sqrt (p / res.2) : ℚ) := by exact_mod_cast hb_pos
    have h10z_pos : (0 : ℚ) < (10 : ℚ) ^ (res.1 : ℤ) := zpow_pos (by norm_num) _
    exact mul_pos hbq_pos h10z_pos

/-- For `x > 0`, `sqrtℚLow x > 0`. -/
private lemma sqrtℚLow_pos_of_pos {y : ℚ} (hy : 0 < y) : 0 < sqrtℚLow y := by
  rw [sqrtℚLow]
  rw [if_neg (not_le.mpr hy)]
  apply sqrtℚLowImpl_pos
  · -- 0 < y.num.toNat
    have hnum_pos : 0 < y.num := Rat.num_pos.mpr hy
    have : (y.num.toNat : ℤ) = y.num := Int.toNat_of_nonneg (le_of_lt hnum_pos)
    omega
  · exact y.pos
  · exact le_refl _

/-- `√x ≤ √⁺ x` for `x ≥ 0` (Definition 47). -/
theorem sqrt_le_sqrtℚUp {x : ℚ} (hx : 0 ≤ x) :
    Real.sqrt ((x : ℚ) : ℝ) ≤ ((sqrtℚUp x : ℚ) : ℝ) := by
  unfold sqrtℚUp
  split_ifs with hx0
  · -- x ≤ 0 and 0 ≤ x → x = 0; sqrt 0 = 0.
    have : x = 0 := le_antisymm hx0 hx
    simp [this]
  · -- 0 < x
    have hx0' : 0 < x := lt_of_le_of_ne hx (fun heq => hx0 (by simp [← heq]))
    set y : ℚ := 1 / x with hy_def
    have hy_pos : 0 < y := by rw [hy_def]; exact one_div_pos.mpr hx0'
    have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
    have hLow_pos_Q : 0 < sqrtℚLow y := sqrtℚLow_pos_of_pos hy_pos
    have hLow_pos_R : (0 : ℝ) < ((sqrtℚLow y : ℚ) : ℝ) := by exact_mod_cast hLow_pos_Q
    have hsq : ((sqrtℚLow y : ℚ) : ℝ) ^ 2 ≤ ((y : ℚ) : ℝ) := sqrtℚLow_sq_le y hy_nonneg
    have hx_R_pos : (0 : ℝ) < ((x : ℚ) : ℝ) := by exact_mod_cast hx0'
    have hy_R : ((y : ℚ) : ℝ) = 1 / ((x : ℚ) : ℝ) := by
      rw [hy_def]; push_cast; ring
    have hcast : (((1 / sqrtℚLow y : ℚ) : ℝ)) = 1 / ((sqrtℚLow y : ℚ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    rw [le_div_iff₀ hLow_pos_R]
    have hsq' : ((sqrtℚLow y : ℚ) : ℝ) ^ 2 ≤ 1 / ((x : ℚ) : ℝ) := by rw [← hy_R]; exact hsq
    rw [le_div_iff₀ hx_R_pos] at hsq'
    have hprod_nn : 0 ≤ Real.sqrt ((x : ℚ) : ℝ) * ((sqrtℚLow y : ℚ) : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hLow_pos_R)
    have h_sq_eq : (Real.sqrt ((x : ℚ) : ℝ) * ((sqrtℚLow y : ℚ) : ℝ)) ^ 2 =
        ((sqrtℚLow y : ℚ) : ℝ) ^ 2 * ((x : ℚ) : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hx_R_pos)]; ring
    have hprod_sq_le : (Real.sqrt ((x : ℚ) : ℝ) * ((sqrtℚLow y : ℚ) : ℝ)) ^ 2 ≤ 1 := by
      rw [h_sq_eq]; exact hsq'
    nlinarith [hprod_nn, hprod_sq_le]

/-- The squared norm is non-negative. -/
private lemma normSqℚ_nonneg {n : ℕ} (v : Fin n → ℚ) : 0 ≤ normSqℚ v := by
  unfold normSqℚ
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- For a rational vector, the lower-norm bounds the true Euclidean norm. -/
theorem normLowℚ_le_norm {n : ℕ} (v : Fin n → ℚ) :
    ((normLowℚ v : ℚ) : ℝ) ≤ Real.sqrt ((normSqℚ v : ℚ) : ℝ) :=
  sqrtℚLow_le_sqrt (normSqℚ_nonneg v)

/-- For a rational vector, the true Euclidean norm bounds the upper-norm. -/
theorem norm_le_normUpℚ {n : ℕ} (v : Fin n → ℚ) :
    Real.sqrt ((normSqℚ v : ℚ) : ℝ) ≤ ((normUpℚ v : ℚ) : ℝ) :=
  sqrt_le_sqrtℚUp (normSqℚ_nonneg v)

def upperSqrt : UpperSqrt where
  f := sqrtℚUp
  bound _ := sqrt_le_sqrtℚUp

def lowerSqrt : LowerSqrt where
  f := sqrtℚLow
  bound _ := sqrtℚLow_le_sqrt

def sqrtApprox : Approx where
  upper_sqrt_two := 1.42
  upper_sqrt_two_gt_sqrt_two := by
    show ((1.42 : ℚ) : ℝ) > Real.sqrt 2
    have h : Real.sqrt 2 < (1.42 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    push_cast
    linarith
  upper_sqrt_five := 2.24
  upper_sqrt_five_gt_sqrt_five := by
    show ((2.24 : ℚ) : ℝ) > Real.sqrt 5
    have h : Real.sqrt 5 < (2.24 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    push_cast
    linarith
  lower_sqrt := lowerSqrt
  upper_sqrt := upperSqrt

end RationalApprox

/-! ## Sanity checks -/
section Examples
open RationalApprox

/-- info: 14142135623 / 10000000000 -/
#guard_msgs in
#eval sqrtℚLow 2

/-- info: 50000000000 / 35355339059 -/
#guard_msgs in
#eval sqrtℚUp 2

/-- info: 35355339059 / 50000000000 -/
#guard_msgs in
#eval sqrtℚLow (1/2)

/-- info: 10000000000 / 14142135623 -/
#guard_msgs in
#eval sqrtℚUp  (1/2)

/-- info: 10 -/
#guard_msgs in
#eval sqrtℚLow 100

/-- info: 10 -/
#guard_msgs in
#eval sqrtℚUp  100

end Examples
