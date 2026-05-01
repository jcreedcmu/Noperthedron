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

A fuel of `1024` is far beyond what is needed for any rational arising in the
proof: each step changes `a` by `1`, and `|a| ≲ digits(x.num) + digits(x.den)`. -/
def findShift (x : ℚ) : ℤ :=
  findShiftAux x 0 1024

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
  sorry

/-- `sqrtℚUp` is non-negative. -/
theorem sqrtℚUp_nonneg (x : ℚ) : 0 ≤ sqrtℚUp x := by
  sorry

/-- `√⁻ x ≤ √x` for `x ≥ 0` (Definition 47). -/
theorem sqrtℚLow_le_sqrt {x : ℚ} (hx : 0 ≤ x) :
    ((sqrtℚLow x : ℚ) : ℝ) ≤ Real.sqrt ((x : ℚ) : ℝ) := by
  sorry

/-- `√x ≤ √⁺ x` for `x ≥ 0` (Definition 47). -/
theorem sqrt_le_sqrtℚUp {x : ℚ} (hx : 0 ≤ x) :
    Real.sqrt ((x : ℚ) : ℝ) ≤ ((sqrtℚUp x : ℚ) : ℝ) := by
  sorry

/-- For a rational vector, the lower-norm bounds the true Euclidean norm. -/
theorem normLowℚ_le_norm {n : ℕ} (v : Fin n → ℚ) :
    ((normLowℚ v : ℚ) : ℝ) ≤ Real.sqrt ((normSqℚ v : ℚ) : ℝ) :=
  sorry -- sqrtℚLow_le_sqrt (by positivity)

/-- For a rational vector, the true Euclidean norm bounds the upper-norm. -/
theorem norm_le_normUpℚ {n : ℕ} (v : Fin n → ℚ) :
    Real.sqrt ((normSqℚ v : ℚ) : ℝ) ≤ ((normUpℚ v : ℚ) : ℝ) :=
  sorry --sqrt_le_sqrtℚUp (by positivity)

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

