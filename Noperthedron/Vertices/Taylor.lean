import Mathlib.Data.Rat.Defs
import Noperthedron.Vertices.Exact
import Noperthedron.Vertices.Trig
import Noperthedron.Vertices.Truncated

namespace Noperthedron

/-- Rational approximation of π, matching Mathlib's `pi_gt_d20` bound. -/
def piQ : ℚ := 3.14159265358979323846

/-- The rational base coordinates of the noperthedron, as a function of i. -/
def Crat : Fin 3 → (Fin 3 → ℚ)
  | 0 => Nopert.C1
  | 1 => Nopert.C2
  | 2 => Nopert.C3

/-- Rational vertex approximation using Taylor-polynomial trig at rational angles.
    This is the intermediate list `nopertListℚ` from `M2D_PLAN.md`.
    Uses angle reduction: for k ≥ 8, evaluates Taylor polynomials at
    2π(15-k)/15 instead of 2πk/15, using cos(2π-x) = cos(x) and
    sin(2π-x) = -sin(x). This keeps all Taylor evaluations at
    angles ≤ 2π·7/15 ≈ 2.93, where the degree-25 remainder is tiny. -/
def nopertPtℚ (k ℓ : ℕ) (i : Fin 3) : Fin 3 → ℚ :=
  let k' := if k ≤ 7 then k else 15 - k
  let θ := 2 * piQ * k' / 15
  let c := cosQ θ
  let s := if k ≤ 7 then sinQ θ else -(sinQ θ)
  let ci := Crat i
  let sgn : ℚ := (-1) ^ ℓ
  fun
  | 0 => sgn * (c * ci 0 - s * ci 1)
  | 1 => sgn * (s * ci 0 + c * ci 1)
  | 2 => sgn * ci 2

/-- The full rational intermediate vertex list (90 entries). -/
def nopertListℚ : Array (Fin 3 → ℚ) :=
  Array.ofFn fun (j : Fin 90) =>
    nopertPtℚ (j.val % 15) (j.val / 45) ⟨(j.val % 45) / 15, by omega⟩
