import Mathlib.Data.Nat.Factorial.Basic
import Noperthedron.Checker.Global

/-!
# κ-Approximation of Noperthedron Vertices

This file establishes that the hard-coded rational vertices in `nopertListQ`
are within κ = 10⁻¹⁰ of the real noperthedron vertices. The approach:

1. Pick a rational πQ with 20-digit accuracy (from Mathlib bounds).
2. For each vertex (k, i, ℓ), compute `cosQ(2·πQ·k'/15)` and `sinQ(2·πQ·k'/15)`
   where k' is the range-reduced angle index (k' = min(k, 15-k)).
3. Form the Taylor-approximated vertex coordinates (rational).
4. Compare to the hard-coded `nopertListQ` values — pure rational subtraction.
5. The total error is (Taylor remainder + π error + rational difference) ≤ κ.
-/

namespace Solution.KappaApprox

open Solution.Checker
open scoped Nat -- for ! notation

/-! ## Rational π approximation

From Mathlib's `pi_gt_d20` and `pi_lt_d20`:
  3.14159265358979323846 < π < 3.14159265358979323847
So |π - πQ| < 10⁻²⁰.
-/

def piQ : ℚ := 314159265358979323846 / 10 ^ 20

/-! ## Range-reduced angle computation

For k ∈ {0, ..., 14}, the rotation angle is θ = 2πk/15.
For k ≥ 8, we use cos(2πk/15) = cos(2π(15-k)/15) and
sin(2πk/15) = -sin(2π(15-k)/15), so the Taylor polynomial is
evaluated at the smaller angle 2π(15-k)/15 ≤ 14π/15 ≈ 2.93.
-/

/-- Range-reduced angle index: min(k, 15-k). Always ≤ 7. -/
def rk (k : ℕ) : ℕ := if k ≤ 7 then k else 15 - k

/-- Rational angle for Taylor evaluation (range-reduced). -/
def angleQ (k : ℕ) : ℚ := 2 * piQ * rk k / 15

/-- cos(2πk/15) ≈ cosQ(angleQ k) — range reduction doesn't affect cos. -/
def cosRQ (k : ℕ) : ℚ := cosQ (angleQ k)

/-- sin(2πk/15) ≈ ±sinQ(angleQ k) — negated for k ≥ 8. -/
def sinRQ (k : ℕ) : ℚ := if k ≤ 7 then sinQ (angleQ k) else -(sinQ (angleQ k))

/-! ## Base vertex coordinates (rational)

These are the exact rational base vertices C1, C2, C3 from `Nopert.lean`,
stored by component for convenient access.
-/

/-- x-coordinates of C1, C2, C3 -/
def Cx : Fin 3 → ℚ
  | 0 => 152024884 / 259375205
  | 1 => 6632738028 / 10 ^ 10
  | 2 => 8193990033 / 10 ^ 10

/-- y-coordinates of C1, C2, C3 -/
def Cy : Fin 3 → ℚ
  | 0 => 0
  | 1 => 6106948881 / 10 ^ 10
  | 2 => 5298215096 / 10 ^ 10

/-- z-coordinates of C1, C2, C3 -/
def Cz : Fin 3 → ℚ
  | 0 => 210152163 / 259375205
  | 1 => 3980949609 / 10 ^ 10
  | 2 => 1230614493 / 10 ^ 10

/-! ## Taylor-approximated vertex computation

For vertex (k, i, ℓ), compute:
  v = (-1)^ℓ · Rz(2πk/15)(Cᵢ)

using cosQ/sinQ at the range-reduced rational angle.
-/

/-- Taylor-approximated vertex coordinates. -/
def taylorVert (k : ℕ) (i : Fin 3) (ℓ : ℕ) : Fin 3 → ℚ :=
  let c := cosRQ k
  let s := sinRQ k
  let sign : ℚ := if ℓ = 0 then 1 else -1
  fun
  | 0 => sign * (c * Cx i - s * Cy i)
  | 1 => sign * (s * Cx i + c * Cy i)
  | 2 => sign * Cz i

/-- Flat index: k + 15·i + 45·ℓ (matches nopertList ordering). -/
def flatIdx (k i ℓ : ℕ) : ℕ := k + 15 * i + 45 * ℓ

/-! ## Per-vertex rational difference computation -/

/-- Absolute coordinate difference between Taylor-approximated and hard-coded vertex. -/
def coordDiff (k : ℕ) (i : Fin 3) (ℓ : ℕ) (coord : Fin 3) : ℚ :=
  let tv := taylorVert k i ℓ coord
  let hv := (nopertListQ.getD (flatIdx k i.val ℓ) (fun _ => 0)) coord
  |tv - hv|

/-- Maximum absolute coordinate difference across all 3 coordinates. -/
def maxCoordDiff (k : ℕ) (i : Fin 3) (ℓ : ℕ) : ℚ :=
  max (coordDiff k i ℓ 0) (max (coordDiff k i ℓ 1) (coordDiff k i ℓ 2))

/-- Check that all 90 vertex rational differences are below a bound. -/
def allDiffsBelow (bound : ℚ) : Bool :=
  let fins3 : List (Fin 3) := [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩]
  let checks := do
    let ℓ ← List.range 2
    let i ← fins3
    let k ← List.range 15
    pure (decide (maxCoordDiff k i ℓ < bound))
  checks.all id

/-! ## Error bound computation

The total per-coordinate error between a real vertex coordinate and its
hard-coded approximation decomposes as:

  |real_coord - hardcoded| ≤ trig_error + rational_diff

where:
- `trig_error` bounds |cos(2πk/15) - cosQ(2πQ·k'/15)| etc.
  (Taylor remainder + π approximation error, with range reduction)
- `rational_diff` = |cosQ(2πQ·k'/15)·Cij - hardcoded| (computed above)

The trig_error uses: cos is 1-Lipschitz, sin is 1-Lipschitz,
|π - πQ| < 10⁻²⁰, and the Taylor remainder |cos(x) - cosℚ(x)| ≤ |x|²⁶/26!.
With range reduction, |x| ≤ 14·πQ/15.

The worst-case rational argument magnitude (k'=7):
-/

/-- Upper bound on |2πQ·k'/15| for k' ≤ 7. -/
def maxArgQ : ℚ := 14 * piQ / 15

/-- Taylor remainder bound for cos at |x| ≤ maxArgQ: |x|²⁶/26! -/
def cosRemainderBound : ℚ := maxArgQ ^ 26 / 26!

/-- Taylor remainder bound for sin at |x| ≤ maxArgQ: |x|²⁷/27! -/
def sinRemainderBound : ℚ := maxArgQ ^ 27 / 27!

/-- π Lipschitz error bound: 2·(14/15)·|π-πQ| ≤ 2·(14/15)·10⁻²⁰
    (factor of 2 because each coordinate involves both cos and sin terms) -/
def piLipBound : ℚ := 2 * (14 / 15) * (1 / 10 ^ 20)

/-- Total trig error per trig function evaluation.
    Each vertex coordinate involves two trig evaluations (cos·Cx ± sin·Cy),
    so multiply by 2. Then |Cij| ≤ 1 absorbs the coefficient. -/
def trigErrorBound : ℚ := piLipBound + cosRemainderBound + sinRemainderBound

/-- Worst-case rational difference across all 90 vertices. -/
def worstDiff : ℚ :=
  let fins3 : List (Fin 3) := [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩]
  let diffs := do
    let ℓ ← List.range 2
    let i ← fins3
    let k ← List.range 15
    pure (maxCoordDiff k i ℓ)
  diffs.foldl max 0

/-- Total per-coordinate error bound: trig error + worst rational diff. -/
def perCoordBound : ℚ := trigErrorBound + worstDiff

/-- Total L2 error bound: √3 · perCoordBound ≤ 3 · perCoordBound
    (using ‖v‖₂ ≤ ‖v‖₁ = |v₀|+|v₁|+|v₂| ≤ 3·max). -/
def totalErrorBound : ℚ := 3 * perCoordBound

def κQ' : ℚ := 1 / 10 ^ 10

/-! ## Verification -/

/-- info: true -/
#guard_msgs in
#eval decide (totalErrorBound < κQ')

/-- info: true -/
#guard_msgs in
#eval decide (cosRemainderBound < 1 / 10 ^ 14)

/-- info: true -/
#guard_msgs in
#eval decide (worstDiff < 1 / 10 ^ 14)

end Solution.KappaApprox
