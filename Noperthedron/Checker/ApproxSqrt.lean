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
* `x > 0`: find the unique `a ∈ ℤ` such that `x · 10^(2a) ∈ [10^20, 10^22)`,
  let `b := ⌊√(x · 10^(2a))⌋`, and set
    `sqrtℚLow x := b / 10^a`,
    `sqrtℚUp  x := 1 / sqrtℚLow (1 / x)`.
  This guarantees ten decimal digits of accuracy.

The construction is implemented as follows:
* `findShift` locates `a` by fuel-bounded iteration starting at `0`.
* `b` is obtained by `Nat.sqrt` applied to natural-number division of
  the (positive) numerator and denominator of `x · 10^(2a)`. This works
  because for any rational `r > 0`, `Nat.sqrt (r.num.toNat / r.den) = ⌊√r⌋`:
  the largest integer with square `≤ r` equals the largest with square
  `≤ ⌊r⌋`, since the squares in question are themselves integers.
-/

namespace RationalApprox

open scoped BigOperators

/-! ## Choosing the scale -/

/-- Auxiliary fuel-bounded search for an integer `a` such that
`x · 10^(2a) ∈ [10^20, 10^22)`. With `0 < x` and enough fuel, the unique
such `a` is returned. -/
private def findShiftAux (x : ℚ) : ℤ → ℕ → ℤ
  | a, 0          => a
  | a, fuel + 1 =>
      let scaled := x * (10 : ℚ) ^ (2 * a)
      if scaled < ((10 : ℚ) ^ (20 : ℕ)) then
        findShiftAux x (a + 1) fuel
      else if ((10 : ℚ) ^ (22 : ℕ)) ≤ scaled then
        findShiftAux x (a - 1) fuel
      else
        a
/-- The unique integer `a` with `x · 10^(2a) ∈ [10^20, 10^22)`, for `x > 0`.

The fuel grows with the magnitude of the input, so the search converges for
any `0 < x`: we have `|a*| ≲ digits(x.num) + digits(x.den)`, where the search
moves by `±1` per step. -/
def findShift (x : ℚ) : ℤ :=
  findShiftAux x 0 (Nat.log 10 x.num.natAbs + Nat.log 10 x.den + 100)

/-! ## The square-root functions -/

/-- **Lower rational square-root** (`√⁻`): returns `0` on `x ≤ 0`; otherwise
returns a rational `r` with `r ≤ √x`. -/
def sqrtℚLow (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else
    let a      := findShift x
    let scaled := x * (10 : ℚ) ^ (2 * a)
    -- For `0 < scaled` we have `0 < scaled.num`, so `.toNat` is well-defined.
    -- `b = ⌊√scaled⌋ = Nat.sqrt (scaled.num.toNat / scaled.den)`.
    let m : ℕ  := scaled.num.toNat / scaled.den
    let b : ℕ  := Nat.sqrt m
    (b : ℚ) * (10 : ℚ) ^ (-a)

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

/-- `sqrtℚLow` is non-negative. -/
theorem sqrtℚLow_nonneg (x : ℚ) : 0 ≤ sqrtℚLow x := by
  unfold sqrtℚLow
  split_ifs with h
  · exact le_refl 0
  · positivity

/-- `sqrtℚUp` is non-negative. -/
theorem sqrtℚUp_nonneg (x : ℚ) : 0 ≤ sqrtℚUp x := by
  unfold sqrtℚUp
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg zero_le_one (sqrtℚLow_nonneg _)

/-- Squared lower bound: `(sqrtℚLow x)^2 ≤ x` (cast to ℝ) for `0 ≤ x`. -/
private lemma sqrtℚLow_sq_le (x : ℚ) (hx : 0 ≤ x) :
    ((sqrtℚLow x : ℚ) : ℝ) ^ 2 ≤ ((x : ℚ) : ℝ) := by
  unfold sqrtℚLow
  split_ifs with h
  · -- x ≤ 0, so sqrtℚLow x = 0; combined with 0 ≤ x means x = 0.
    have hx0 : x = 0 := le_antisymm h hx
    simp [hx0]
  · -- 0 < x
    have h : 0 < x := lt_of_le_of_ne hx (fun heq => h (by simp [← heq]))
    set a := findShift x with ha
    set scaled : ℚ := x * (10 : ℚ) ^ (2 * a) with hscaled
    set m : ℕ := scaled.num.toNat / scaled.den with hm
    set b : ℕ := Nat.sqrt m with hb
    -- Goal: ((b : ℚ) * (10 : ℚ)^(-a))^2 ≤ x in ℝ.
    have h10pos : (0 : ℝ) < (10 : ℝ) ^ (2 * a) := by positivity
    have hscaled_pos : 0 < scaled := by
      simp [hscaled]; exact mul_pos h (by positivity)
    have hscaled_num_pos : 0 < scaled.num := Rat.num_pos.mpr hscaled_pos
    have hscaled_den_pos : (0 : ℤ) < scaled.den := by exact_mod_cast scaled.pos
    -- (m : ℝ) ≤ (scaled : ℝ)
    have hm_le_scaled : (m : ℝ) ≤ (scaled : ℝ) := by
      have h1 : m * scaled.den ≤ scaled.num.toNat := Nat.div_mul_le_self _ _
      have htoNat : (scaled.num.toNat : ℤ) = scaled.num :=
        Int.toNat_of_nonneg (le_of_lt hscaled_num_pos)
      have h2 : (m : ℤ) * (scaled.den : ℤ) ≤ scaled.num := by
        have := h1
        have h3 : ((m * scaled.den : ℕ) : ℤ) ≤ ((scaled.num.toNat : ℕ) : ℤ) := by
          exact_mod_cast h1
        rw [Nat.cast_mul, Int.toNat_of_nonneg (le_of_lt hscaled_num_pos)] at h3
        exact h3
      have h4 : (m : ℝ) * (scaled.den : ℝ) ≤ (scaled.num : ℝ) := by exact_mod_cast h2
      have hden_pos_R : (0 : ℝ) < (scaled.den : ℝ) := by exact_mod_cast hscaled_den_pos
      have : (m : ℝ) ≤ (scaled.num : ℝ) / (scaled.den : ℝ) :=
        (le_div_iff₀ hden_pos_R).mpr h4
      have hcast : ((scaled : ℚ) : ℝ) = (scaled.num : ℝ) / (scaled.den : ℝ) := by
        rw [Rat.cast_def]
      rw [hcast]
      exact this
    -- (b : ℝ)^2 ≤ (m : ℝ)
    have hbb_le_m : (b : ℝ) ^ 2 ≤ (m : ℝ) := by
      have : b * b ≤ m := Nat.sqrt_le m
      have : (b * b : ℕ) ≤ (m : ℕ) := this
      have hRR : ((b * b : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast this
      simpa [pow_two, Nat.cast_mul] using hRR
    -- Combine: (b : ℝ)^2 ≤ (scaled : ℝ)
    have hbb_le_scaled : (b : ℝ) ^ 2 ≤ ((scaled : ℚ) : ℝ) := le_trans hbb_le_m hm_le_scaled
    -- ((b : ℝ) * 10^(-a))^2 = (b : ℝ)^2 * 10^(-2a)
    -- And (scaled : ℝ) * 10^(-2a) = (x : ℝ).
    have h10a_pos : (0 : ℝ) < (10 : ℝ) ^ ((-2 * a : ℤ)) := by positivity
    have hscaled_cast : ((scaled : ℚ) : ℝ) = (x : ℝ) * (10 : ℝ) ^ (2 * a) := by
      show (((x * (10 : ℚ) ^ (2 * a)) : ℚ) : ℝ) = _
      push_cast
      rfl
    -- multiply both sides of hbb_le_scaled by 10^(-2a) > 0
    have hmul : (b : ℝ) ^ 2 * (10 : ℝ) ^ ((-2 * a : ℤ)) ≤
        ((scaled : ℚ) : ℝ) * (10 : ℝ) ^ ((-2 * a : ℤ)) :=
      mul_le_mul_of_nonneg_right hbb_le_scaled (le_of_lt h10a_pos)
    have h10ne : (10 : ℝ) ≠ 0 := by norm_num
    have hRHS : ((scaled : ℚ) : ℝ) * (10 : ℝ) ^ ((-2 * a : ℤ)) = (x : ℝ) := by
      rw [hscaled_cast, mul_assoc, ← zpow_add₀ h10ne]
      have : (2 * a : ℤ) + (-2 * a : ℤ) = 0 := by ring
      rw [this]
      simp
    -- LHS rewriting
    have hLHS_eq : (((b : ℚ) * (10 : ℚ) ^ (-a) : ℚ) : ℝ) ^ 2 =
        (b : ℝ) ^ 2 * (10 : ℝ) ^ ((-2 * a : ℤ)) := by
      push_cast
      rw [mul_pow]
      have : ((10 : ℝ) ^ (-a)) ^ 2 = (10 : ℝ) ^ ((-2 * a : ℤ)) := by
        rw [← zpow_natCast _ 2, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [this]
    rw [hLHS_eq, ← hRHS]
    exact hmul

/-- `√⁻ x ≤ √x` for `x ≥ 0` (Definition 47). -/
theorem sqrtℚLow_le_sqrt {x : ℚ} (hx : 0 ≤ x) :
    ((sqrtℚLow x : ℚ) : ℝ) ≤ Real.sqrt ((x : ℚ) : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  exact sqrtℚLow_sq_le x hx

/-! ### Correctness of `findShiftAux`

For `0 < x`, with sufficient fuel, `findShiftAux x a fuel` returns an integer
`a'` such that `x * 10^(2a') ∈ [10^20, 10^22)`. The proof builds up:
1. If already in `[10^20, 10^22)`, the function returns `a`.
2. Up-search converges: starting strictly below, multiplying by `100` each
   step we cross into the window (and never overshoot, since the window has
   multiplicative width `100`).
3. Down-search converges: symmetric.
4. The fuel bound `Nat.log 10 num + Nat.log 10 den + 100` always suffices.
-/

/-- The "in window" predicate for the scale search. -/
private def InWindow (x : ℚ) (a : ℤ) : Prop :=
  ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * a) ∧
    x * (10 : ℚ) ^ (2 * a) < ((10 : ℚ) ^ (22 : ℕ))

/-- If we are already in the target window, `findShiftAux` returns the current `a`. -/
private lemma findShiftAux_of_inWindow (x : ℚ) (a : ℤ) (fuel : ℕ)
    (hw : InWindow x a) : findShiftAux x a fuel = a := by
  cases fuel with
  | zero => rfl
  | succ n =>
    obtain ⟨hlo, hhi⟩ := hw
    unfold findShiftAux
    simp only
    have h1 : ¬ (x * (10 : ℚ) ^ (2 * a) < (10 : ℚ) ^ (20 : ℕ)) := not_lt.mpr hlo
    have h2 : ¬ ((10 : ℚ) ^ (22 : ℕ) ≤ x * (10 : ℚ) ^ (2 * a)) := not_le.mpr hhi
    rw [if_neg h1, if_neg h2]

/-- Stepping `a` up by 1 multiplies the scaled value by 100. -/
private lemma scaled_step_up (x : ℚ) (a : ℤ) :
    x * (10 : ℚ) ^ (2 * (a + 1)) = x * (10 : ℚ) ^ (2 * a) * 100 := by
  have h10ne : (10 : ℚ) ≠ 0 := by norm_num
  have hrw : (10 : ℚ) ^ (2 * (a + 1)) = (10 : ℚ) ^ (2 * a) * (10 : ℚ) ^ 2 := by
    have heq : (2 * (a + 1) : ℤ) = 2 * a + 2 := by ring
    rw [heq, zpow_add₀ h10ne]
    rfl
  rw [hrw]; ring

/-- Stepping `a` down by 1 divides the scaled value by 100. -/
private lemma scaled_step_down (x : ℚ) (a : ℤ) :
    x * (10 : ℚ) ^ (2 * (a - 1)) * 100 = x * (10 : ℚ) ^ (2 * a) := by
  have h10ne : (10 : ℚ) ≠ 0 := by norm_num
  have hrw : (10 : ℚ) ^ (2 * a) = (10 : ℚ) ^ (2 * (a - 1)) * (10 : ℚ) ^ 2 := by
    have heq : (2 * a : ℤ) = 2 * (a - 1) + 2 := by ring
    rw [heq, zpow_add₀ h10ne]
    rfl
  rw [hrw]; ring

/-- **Up-search convergence**: if `0 < x`, currently `scaled := x * 10^(2a) < 10^22`,
and `scaled * 100^k ≥ 10^20` for some `k : ℕ`, then `findShiftAux x a fuel`
returns a result in the window provided `fuel ≥ k`.

Note: maintaining the invariant `scaled < 10^22` is automatic because each
"up" step is taken only when `scaled < 10^20`, which then yields
`scaled * 100 < 10^22`. -/
private lemma findShiftAux_up {x : ℚ} (hx : 0 < x) :
    ∀ (k : ℕ) (a : ℤ),
      x * (10 : ℚ) ^ (2 * a) < ((10 : ℚ) ^ (22 : ℕ)) →
      ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * a) * (100 : ℚ) ^ k →
      ∀ fuel, k ≤ fuel → InWindow x (findShiftAux x a fuel) := by
  intro k
  induction k with
  | zero =>
    intro a hhi hlo fuel _
    -- scaled * 100^0 = scaled, so 10^20 ≤ scaled < 10^22 means in window.
    have hlo' : ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * a) := by
      simpa using hlo
    have hw : InWindow x a := ⟨hlo', hhi⟩
    rw [findShiftAux_of_inWindow x a fuel hw]
    exact hw
  | succ j ih =>
    intro a hhi hlo fuel hfuel
    by_cases hcase : x * (10 : ℚ) ^ (2 * a) < ((10 : ℚ) ^ (20 : ℕ))
    · -- scaled too low: step up. Apply IH at a+1 with k=j.
      cases fuel with
      | zero => omega
      | succ f =>
        unfold findShiftAux
        simp only
        rw [if_pos hcase]
        -- New scaled = old scaled * 100; need new < 10^22.
        have hnew_eq : x * (10 : ℚ) ^ (2 * (a + 1)) = x * (10 : ℚ) ^ (2 * a) * 100 :=
          scaled_step_up x a
        have hnew_lt : x * (10 : ℚ) ^ (2 * (a + 1)) < ((10 : ℚ) ^ (22 : ℕ)) := by
          rw [hnew_eq]
          have hpos : (0 : ℚ) < 100 := by norm_num
          have h1 : x * (10 : ℚ) ^ (2 * a) * 100 < ((10 : ℚ) ^ (20 : ℕ)) * 100 := by
            exact mul_lt_mul_of_pos_right hcase hpos
          have h2 : ((10 : ℚ) ^ (20 : ℕ)) * 100 = (10 : ℚ) ^ (22 : ℕ) := by norm_num
          linarith
        -- New 100^j bound:
        -- old: 10^20 ≤ x * 10^(2a) * 100^(j+1) = (x * 10^(2(a+1))) * 100^j
        have hnew_lo : ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * (a + 1)) * (100 : ℚ) ^ j := by
          have : x * (10 : ℚ) ^ (2 * a) * (100 : ℚ) ^ (j + 1) =
                 x * (10 : ℚ) ^ (2 * (a + 1)) * (100 : ℚ) ^ j := by
            rw [hnew_eq, pow_succ]; ring
          linarith [this ▸ hlo]
        exact ih (a + 1) hnew_lt hnew_lo f (Nat.le_of_succ_le_succ hfuel)
    · -- scaled ≥ 10^20: combined with hhi, in window.
      push_neg at hcase
      have hw : InWindow x a := ⟨hcase, hhi⟩
      rw [findShiftAux_of_inWindow x a fuel hw]
      exact hw

/-- **Down-search convergence**: symmetric to `findShiftAux_up`. -/
private lemma findShiftAux_down {x : ℚ} (hx : 0 < x) :
    ∀ (k : ℕ) (a : ℤ),
      ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * a) →
      x * (10 : ℚ) ^ (2 * a) < ((10 : ℚ) ^ (22 : ℕ)) * (100 : ℚ) ^ k →
      ∀ fuel, k ≤ fuel → InWindow x (findShiftAux x a fuel) := by
  intro k
  induction k with
  | zero =>
    intro a hlo hhi fuel _
    have hhi' : x * (10 : ℚ) ^ (2 * a) < ((10 : ℚ) ^ (22 : ℕ)) := by
      simpa using hhi
    have hw : InWindow x a := ⟨hlo, hhi'⟩
    rw [findShiftAux_of_inWindow x a fuel hw]
    exact hw
  | succ j ih =>
    intro a hlo hhi fuel hfuel
    by_cases hcase : ((10 : ℚ) ^ (22 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * a)
    · -- scaled too high: step down. New scaled = old / 100.
      cases fuel with
      | zero => omega
      | succ f =>
        unfold findShiftAux
        simp only
        have hnotlo : ¬ (x * (10 : ℚ) ^ (2 * a) < ((10 : ℚ) ^ (20 : ℕ))) := by
          push_neg
          calc ((10 : ℚ) ^ (20 : ℕ)) ≤ ((10 : ℚ) ^ (22 : ℕ)) := by norm_num
            _ ≤ x * (10 : ℚ) ^ (2 * a) := hcase
        rw [if_neg hnotlo, if_pos hcase]
        -- Recurse at a-1. New scaled = old scaled / 100.
        have hnew_eq : x * (10 : ℚ) ^ (2 * (a - 1)) * 100 = x * (10 : ℚ) ^ (2 * a) :=
          scaled_step_down x a
        -- 10^20 ≤ new_scaled? old ≥ 10^22 ≥ 10^20*100, so new ≥ 10^20.
        have hnew_lo : ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * (a - 1)) := by
          have h1 : ((10 : ℚ) ^ (22 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * (a - 1)) * 100 := by
            rw [hnew_eq]; exact hcase
          have h22eq : ((10 : ℚ) ^ (22 : ℕ)) = ((10 : ℚ) ^ (20 : ℕ)) * 100 := by norm_num
          have h2 : ((10 : ℚ) ^ (20 : ℕ)) * 100 ≤ x * (10 : ℚ) ^ (2 * (a - 1)) * 100 := by
            rw [← h22eq]; exact h1
          have hpos : (0 : ℚ) < 100 := by norm_num
          exact le_of_mul_le_mul_right h2 hpos
        -- new_scaled < 10^22 * 100^j:
        -- old / 100 < 10^22 * 100^(j+1) / 100 = 10^22 * 100^j (for j ≥ 0).
        have hnew_hi : x * (10 : ℚ) ^ (2 * (a - 1)) < ((10 : ℚ) ^ (22 : ℕ)) * (100 : ℚ) ^ j := by
          have h1 : x * (10 : ℚ) ^ (2 * (a - 1)) * 100 < ((10 : ℚ) ^ (22 : ℕ)) * (100 : ℚ) ^ (j + 1) := by
            rw [hnew_eq]; exact hhi
          have h2 : ((10 : ℚ) ^ (22 : ℕ)) * (100 : ℚ) ^ (j + 1) =
                    (((10 : ℚ) ^ (22 : ℕ)) * (100 : ℚ) ^ j) * 100 := by
            rw [pow_succ]; ring
          rw [h2] at h1
          have hpos : (0 : ℚ) < 100 := by norm_num
          exact lt_of_mul_lt_mul_right h1 (by positivity)
        exact ih (a - 1) hnew_lo hnew_hi f (Nat.le_of_succ_le_succ hfuel)
    · -- scaled < 10^22: combined with hlo, in window.
      push_neg at hcase
      have hw : InWindow x a := ⟨hlo, hcase⟩
      rw [findShiftAux_of_inWindow x a fuel hw]
      exact hw

/-- `Nat.log 10 n` provides an upper bound: `n < 10^(Nat.log 10 n + 1)`. -/
private lemma nat_lt_ten_pow_log_succ (n : ℕ) :
    (n : ℚ) < (10 : ℚ) ^ (Nat.log 10 n + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) n
  have hcast : (n : ℚ) < ((10 ^ (Nat.log 10 n + 1) : ℕ) : ℚ) := by exact_mod_cast h
  rw [Nat.cast_pow] at hcast
  exact_mod_cast hcast

/-- Useful: `0 < x.num.natAbs` for `0 < x`. -/
private lemma num_natAbs_pos {x : ℚ} (hx : 0 < x) : 0 < x.num.natAbs :=
  Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hx))

/-- For `0 < x`, `x ≥ 1 / x.den` since `x.num ≥ 1`. -/
private lemma rat_ge_one_div_den {x : ℚ} (hx : 0 < x) :
    (1 : ℚ) / (x.den : ℚ) ≤ x := by
  have hd_pos : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.pos
  have hnum_pos : 0 < x.num := Rat.num_pos.mpr hx
  have hnum_ge_one : (1 : ℚ) ≤ (x.num : ℚ) := by exact_mod_cast hnum_pos
  rw [div_le_iff₀ hd_pos]
  -- 1 * den ≤ x * den, i.e., den ≤ x * den = num
  have : x * (x.den : ℚ) = (x.num : ℚ) := by
    rw [Rat.mul_den_eq_num]
  rw [this]
  linarith

/-- For `0 < x`, `x ≤ x.num.natAbs` since `x.den ≥ 1`. -/
private lemma rat_le_num {x : ℚ} (hx : 0 < x) :
    x ≤ (x.num.natAbs : ℚ) := by
  have hd_pos : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.pos
  have hd_ge : (1 : ℚ) ≤ (x.den : ℚ) := by exact_mod_cast x.pos
  have hnum_pos : 0 < x.num := Rat.num_pos.mpr hx
  have hnum_natAbs : (x.num.natAbs : ℚ) = (x.num : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_pos hnum_pos]
  rw [hnum_natAbs]
  -- x ≤ num: since x * den = num and den ≥ 1, x ≤ x * den = num.
  have hxd : x * (x.den : ℚ) = (x.num : ℚ) := by
    rw [Rat.mul_den_eq_num]
  have hpos : 0 ≤ x := le_of_lt hx
  nlinarith [hpos, hd_ge, hxd]

/-- `(100:ℚ)^k = (10:ℚ)^(2k)`. -/
private lemma pow_hundred_eq (k : ℕ) : (100 : ℚ) ^ k = (10 : ℚ) ^ (2 * k) := by
  rw [show (100 : ℚ) = 10 ^ 2 from by norm_num, ← pow_mul, mul_comm]

/-- For `0 < x`, `findShiftAux x 0 fuel` is in window when fuel is large enough. -/
private lemma findShift_inWindow {x : ℚ} (hx : 0 < x) :
    InWindow x (findShift x) := by
  unfold findShift
  set N := Nat.log 10 x.num.natAbs with hN
  set D := Nat.log 10 x.den with hD
  -- Case split: is x < 10^22 or not?
  by_cases hcase : x < ((10 : ℚ) ^ (22 : ℕ))
  · -- Up-search. Use k = D + 11. Then 2k = 2D + 22.
    set k : ℕ := D + 11 with hk
    have hkbound : ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * (0 : ℤ)) * (100 : ℚ) ^ k := by
      simp only [mul_zero, zpow_zero, mul_one]
      -- x * 100^k ≥ (1/den) * 10^(2k) ≥ (1/10^(D+1)) * 10^(2D+22) = 10^(D+21) ≥ 10^20.
      rw [pow_hundred_eq]
      have hx_lb : (1 : ℚ) / (x.den : ℚ) ≤ x := rat_ge_one_div_den hx
      have hden_lt : (x.den : ℚ) < (10 : ℚ) ^ (D + 1) := nat_lt_ten_pow_log_succ x.den
      have hden_pos : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.pos
      have h10pos : (0 : ℚ) < (10 : ℚ) ^ (D + 1) := by positivity
      have hinv : (1 : ℚ) / (10 : ℚ) ^ (D + 1) ≤ 1 / (x.den : ℚ) :=
        le_of_lt (one_div_lt_one_div_of_lt hden_pos hden_lt)
      have hxd : (1 : ℚ) / (10 : ℚ) ^ (D + 1) ≤ x := le_trans hinv hx_lb
      have h10ne : (10 : ℚ) ≠ 0 := by norm_num
      -- Now 10^20 ≤ 1/10^(D+1) * 10^(2k):
      have h2k : 2 * k = 2 * D + 22 := by rw [hk]; ring
      have hsplit : (10 : ℚ) ^ (2 * k) = (10 : ℚ) ^ (D + 1) * (10 : ℚ) ^ (D + 21) := by
        rw [← pow_add]
        congr 1
        omega
      have h_eq : (1 : ℚ) / (10 : ℚ) ^ (D + 1) * (10 : ℚ) ^ (2 * k) = (10 : ℚ) ^ (D + 21) := by
        rw [hsplit]
        field_simp
      have hge_20 : ((10 : ℚ) ^ (20 : ℕ)) ≤ (10 : ℚ) ^ (D + 21) := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 10)
        omega
      have hpos2k : (0 : ℚ) < (10 : ℚ) ^ (2 * k) := by positivity
      calc ((10 : ℚ) ^ (20 : ℕ))
          ≤ (10 : ℚ) ^ (D + 21) := hge_20
        _ = (1 : ℚ) / (10 : ℚ) ^ (D + 1) * (10 : ℚ) ^ (2 * k) := h_eq.symm
        _ ≤ x * (10 : ℚ) ^ (2 * k) :=
            mul_le_mul_of_nonneg_right hxd (le_of_lt hpos2k)
    have hfuel : k ≤ N + D + 100 := by rw [hk]; omega
    have hhi0 : x * (10 : ℚ) ^ (2 * (0 : ℤ)) < ((10 : ℚ) ^ (22 : ℕ)) := by
      simp only [mul_zero, zpow_zero, mul_one]; exact hcase
    exact findShiftAux_up hx k 0 hhi0 hkbound (N + D + 100) hfuel
  · -- Down-search. x ≥ 10^22. Use k = N.
    push_neg at hcase
    set k : ℕ := N with hk
    have hkbound : x * (10 : ℚ) ^ (2 * (0 : ℤ)) < ((10 : ℚ) ^ (22 : ℕ)) * (100 : ℚ) ^ k := by
      simp only [mul_zero, zpow_zero, mul_one]
      rw [pow_hundred_eq]
      -- Need x < 10^22 * 10^(2k) = 10^(22 + 2k).
      have hx_le_num : x ≤ (x.num.natAbs : ℚ) := rat_le_num hx
      have hnum_lt : (x.num.natAbs : ℚ) < (10 : ℚ) ^ (N + 1) := nat_lt_ten_pow_log_succ x.num.natAbs
      have hexp : ((10 : ℚ) ^ (22 : ℕ)) * (10 : ℚ) ^ (2 * k) = (10 : ℚ) ^ (22 + 2 * k) := by
        rw [← pow_add]
      rw [hexp]
      calc x ≤ (x.num.natAbs : ℚ) := hx_le_num
        _ < (10 : ℚ) ^ (N + 1) := hnum_lt
        _ ≤ (10 : ℚ) ^ (22 + 2 * k) := by
            apply pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 10)
            rw [hk]; omega
    have hlo0 : ((10 : ℚ) ^ (20 : ℕ)) ≤ x * (10 : ℚ) ^ (2 * (0 : ℤ)) := by
      simp only [mul_zero, zpow_zero, mul_one]
      calc ((10 : ℚ) ^ (20 : ℕ)) ≤ ((10 : ℚ) ^ (22 : ℕ)) := by norm_num
        _ ≤ x := hcase
    have hfuel : k ≤ N + D + 100 := by rw [hk]; omega
    exact findShiftAux_down hx k 0 hlo0 hkbound (N + D + 100) hfuel

private lemma sqrtℚLow_pos_of_pos {y : ℚ} (hy : 0 < y) : 0 < sqrtℚLow y := by
  unfold sqrtℚLow
  have hy_nle : ¬ (y ≤ 0) := not_le.mpr hy
  rw [if_neg hy_nle]
  set a := findShift y with ha
  set scaled : ℚ := y * (10 : ℚ) ^ (2 * a) with hscaled
  set m : ℕ := scaled.num.toNat / scaled.den with hm
  set b : ℕ := Nat.sqrt m with hb
  -- Goal: 0 < (b : ℚ) * 10^(-a)
  -- We need 0 < b. By in-window, scaled ≥ 10^20, so m ≥ 1.
  have hwin : InWindow y a := findShift_inWindow hy
  obtain ⟨hlo, _⟩ := hwin
  -- scaled ≥ 10^20 ≥ 1
  have hscaled_ge_one : (1 : ℚ) ≤ scaled := by
    rw [hscaled]
    calc (1 : ℚ) ≤ (10 : ℚ) ^ (20 : ℕ) := by norm_num
      _ ≤ y * (10 : ℚ) ^ (2 * a) := hlo
  have hscaled_pos : 0 < scaled := lt_of_lt_of_le zero_lt_one hscaled_ge_one
  -- num ≥ den. Since 1 ≤ scaled = num/den (with den > 0), we have num ≥ den.
  have hden_pos : 0 < scaled.den := scaled.pos
  have hnum_pos : 0 < scaled.num := Rat.num_pos.mpr hscaled_pos
  have hnum_ge_den : (scaled.den : ℤ) ≤ scaled.num := by
    have hx_eq : scaled = (scaled.num : ℚ) / (scaled.den : ℚ) := (Rat.num_div_den scaled).symm
    have hd_pos : (0 : ℚ) < (scaled.den : ℚ) := by exact_mod_cast hden_pos
    have h1 : (1 : ℚ) * (scaled.den : ℚ) ≤ (scaled.num : ℚ) := by
      have := hscaled_ge_one
      rw [hx_eq] at this
      rw [le_div_iff₀ hd_pos] at this
      exact this
    rw [one_mul] at h1
    exact_mod_cast h1
  -- m = num.toNat / den ≥ 1
  have hm_ge_one : 1 ≤ m := by
    rw [hm]
    apply Nat.one_le_div_iff hden_pos |>.mpr
    have : (scaled.den : ℤ) ≤ (scaled.num.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (le_of_lt hnum_pos)]
      exact hnum_ge_den
    exact_mod_cast this
  -- b = Nat.sqrt m ≥ Nat.sqrt 1 = 1
  have hb_ge_one : 1 ≤ b := by
    rw [hb]
    have : Nat.sqrt 1 ≤ Nat.sqrt m := Nat.sqrt_le_sqrt hm_ge_one
    simpa using this
  have hb_pos : (0 : ℚ) < (b : ℚ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hb_ge_one)
  have h10a_pos : (0 : ℚ) < (10 : ℚ) ^ (-a) := by positivity
  exact mul_pos hb_pos h10a_pos

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
    -- Real-cast of x is positive
    have hx_R_pos : (0 : ℝ) < ((x : ℚ) : ℝ) := by exact_mod_cast hx0'
    have hy_R : ((y : ℚ) : ℝ) = 1 / ((x : ℚ) : ℝ) := by
      rw [hy_def]; push_cast; ring
    -- (1 / sqrtℚLow y : ℚ) cast to ℝ is 1 / ((sqrtℚLow y : ℚ) : ℝ)
    have hcast : (((1 / sqrtℚLow y : ℚ) : ℝ)) = 1 / ((sqrtℚLow y : ℚ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    -- Goal: √x ≤ 1 / sqrtℚLow y
    rw [le_div_iff₀ hLow_pos_R]
    -- Goal: √x * sqrtℚLow y ≤ 1
    -- (sqrtℚLow y)^2 ≤ y = 1/x. Multiply by x > 0: (sqrtℚLow y)^2 * x ≤ 1.
    have hsq' : ((sqrtℚLow y : ℚ) : ℝ) ^ 2 ≤ 1 / ((x : ℚ) : ℝ) := by rw [← hy_R]; exact hsq
    have hsq_x : ((sqrtℚLow y : ℚ) : ℝ) ^ 2 * ((x : ℚ) : ℝ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hsq' (le_of_lt hx_R_pos)
      rw [div_mul_cancel₀ _ (ne_of_gt hx_R_pos)] at this
      exact this
    -- So (sqrtℚLow y * √x)^2 ≤ 1.
    have hprod_nn : 0 ≤ Real.sqrt ((x : ℚ) : ℝ) * ((sqrtℚLow y : ℚ) : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hLow_pos_R)
    have h_sq_eq : (Real.sqrt ((x : ℚ) : ℝ) * ((sqrtℚLow y : ℚ) : ℝ)) ^ 2 =
        ((sqrtℚLow y : ℚ) : ℝ) ^ 2 * ((x : ℚ) : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hx_R_pos)]
      ring
    have hprod_sq_le : (Real.sqrt ((x : ℚ) : ℝ) * ((sqrtℚLow y : ℚ) : ℝ)) ^ 2 ≤ 1 := by
      rw [h_sq_eq]; exact hsq_x
    -- From a² ≤ 1 and a ≥ 0, conclude a ≤ 1.
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

end RationalApprox

/-
/-! ## Sanity checks -/
section Examples
open RationalApprox

-- `√2 ≈ 1.41421356237…`. We expect `sqrtℚLow 2` slightly below and
-- `sqrtℚUp 2` slightly above.
#eval sqrtℚLow 2          -- 14142135623 / 10000000000
#eval sqrtℚUp 2

-- `√(1/2) ≈ 0.70710678118…`.
#eval sqrtℚLow (1/2)
#eval sqrtℚUp  (1/2)

-- `√100 = 10`; the lower rational sqrt should match exactly,
-- though `b = 10^11` because of the chosen scale.
#eval sqrtℚLow 100
#eval sqrtℚUp  100

end Examples
-/

