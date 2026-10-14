module

public import Cayley.Checker.QI

@[expose] public section

/-!
# Dense multivariate polynomials over the dyadic rationals

`Poly n` is a polynomial in the variables `t₀, …, t_{n-1}`, stored densely and nested
by the first variable: a `Poly (n+1)` is the list `[c₀, c₁, …]` of `Poly n` coefficients
of `t₀^0, t₀^1, …`. Every variable ranges over `[-1, 1]` (box coordinates are
normalized as `x = centre + half · t`), and `Poly.bounds` encloses the values there.

This file is Mathlib-free; `Cayley.Soundness.Poly` proves the evaluation lemmas.
-/

namespace Cayley

/-- Dense polynomials in `n` variables with dyadic coefficients. -/
abbrev Poly : Nat → Type
  | 0 => QI
  | n + 1 => List (Poly n)

namespace Poly

/-- The coefficient of a constant polynomial. -/
@[inline] def toD (a : Poly 0) : QI := a
/-- A constant polynomial. -/
@[inline] def ofD (a : QI) : Poly 0 := a

/-- Pointwise combination of two lists, keeping the tail of the longer one. -/
def zipLong {α : Type} (f : α → α → α) : List α → List α → List α
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => f x y :: zipLong f xs ys

def zero : (n : Nat) → Poly n
  | 0 => ofD 0
  | _ + 1 => ([] : List _)

def const : (n : Nat) → QI → Poly n
  | 0, c => ofD c
  | n + 1, c => [const n c]

def add : (n : Nat) → Poly n → Poly n → Poly n
  | 0, a, b => ofD (toD a + toD b)
  | n + 1, a, b => zipLong (add n) a b

def neg : (n : Nat) → Poly n → Poly n
  | 0, a => ofD (-toD a)
  | n + 1, a => List.map (neg n) a

def sub (n : Nat) (a b : Poly n) : Poly n := add n a (neg n b)

/-- Multiplication by a dyadic constant. -/
def smul : (n : Nat) → QI → Poly n → Poly n
  | 0, c, a => ofD (c * toD a)
  | n + 1, c, a => List.map (smul n c) a

/-- Convolution of coefficient lists. -/
def mulList {α : Type} (add : α → α → α) (mul : α → α → α) (zero : α) :
    List α → List α → List α
  | [], _ => []
  | x :: xs, b => zipLong add (b.map (mul x)) (zero :: mulList add mul zero xs b)

def mul : (n : Nat) → Poly n → Poly n → Poly n
  | 0, a, b => ofD (toD a * toD b)
  | n + 1, a, b => mulList (add n) (mul n) (zero n) a b

/-- The variable `t_i` scaled and shifted: `c + h · t_i` (and the constant `c` when `i ≥ n`). -/
def var : (n : Nat) → Nat → QI → QI → Poly n
  | 0, _, c, _ => ofD c
  | n + 1, 0, c, h => [const n c, const n h]
  | n + 1, i + 1, c, h => [var n i c h]

def dmin (a b : QI) : QI := if a ≤ b then a else b
def dmax (a b : QI) : QI := if a ≤ b then b else a
def dabs (a : QI) : QI := dmax a (-a)

/-- Enclose `Σ_{k ≥ start} c_k t^k` for `t ∈ [-1,1]`, given enclosures of the `c_k`. -/
def boundsTail : Nat → List (QI × QI) → QI × QI
  | _, [] => (0, 0)
  | k, (lo, hi) :: rest =>
    let (rlo, rhi) := boundsTail (k + 1) rest
    if k % 2 = 0 then (dmin 0 lo + rlo, dmax 0 hi + rhi)
    else
      let m := dmax (dabs lo) (dabs hi)
      (rlo - m, rhi + m)

/-- An enclosure `(lo, hi)` of the values on `[-1,1]^n`. -/
def bounds : (n : Nat) → Poly n → QI × QI
  | 0, a => (toD a, toD a)
  | _ + 1, [] => (0, 0)
  | n + 1, c :: cs =>
    let (lo, hi) := bounds n c
    let (rlo, rhi) := boundsTail 1 (cs.map (bounds n))
    (lo + rlo, hi + rhi)

def lower (n : Nat) (p : Poly n) : QI := (bounds n p).1

/-- The constant coefficient. -/
def constCoeff : (n : Nat) → Poly n → QI
  | 0, a => toD a
  | _ + 1, [] => 0
  | n + 1, c :: _ => constCoeff n c

/-- The sum of the absolute values of all coefficients. -/
def absSum : (n : Nat) → Poly n → QI
  | 0, a => dabs (toD a)
  | n + 1, cs => cs.foldr (fun c acc => absSum n c + acc) 0

/-- The coefficient of `t_i` (degree one in `t_i`, zero in the others). -/
def linCoeff : (n : Nat) → Nat → Poly n → QI
  | 0, _, _ => 0
  | _ + 1, 0, [] => 0
  | _ + 1, 0, [_] => 0
  | n + 1, 0, _ :: c1 :: _ => constCoeff n c1
  | _ + 1, _ + 1, [] => 0
  | n + 1, i + 1, c :: _ => linCoeff n i c

end Poly

end Cayley

end
