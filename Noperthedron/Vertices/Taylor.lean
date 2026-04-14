import Mathlib.Data.Rat.Defs
import Noperthedron.Vertices.Exact
import Noperthedron.Vertices.Index
import Noperthedron.Vertices.Trig

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
    2π(k - 15)/15 instead of 2πk/15. This keeps all Taylor evaluations at
    angles with absolute value ≤ 2π·7/15 ≈ 2.93, where the degree-25 remainder is tiny. -/
def taylorVertex (idx : VertexIndex) : Fin 3 → ℚ :=
  let ⟨k, ℓ, i⟩ := idx
  let k' := if k ≤ 7 then (k : ℚ) else (k : ℚ) - 15
  let θ := 2 * piQ * k' / 15
  let c := cosQ θ
  let s := sinQ θ
  let ci := Crat i
  let sgn : ℚ := (-1) ^ ℓ.val
  fun
  | 0 => sgn * (c * ci 0 - s * ci 1)
  | 1 => sgn * (s * ci 0 + c * ci 1)
  | 2 => sgn * ci 2

lemma taylorVertex_eq_vec (k : Fin 15) (ℓ : Fin 2) (i : Fin 3) :
    let k' := if k ≤ 7 then (k : ℚ) else (k : ℚ) - 15
    let θ := 2 * piQ * k' / 15
    taylorVertex ⟨k, ℓ, i⟩ =
      (-1) ^ ℓ.val • ![cosQ θ * Crat i 0 - sinQ θ * Crat i 1,
                       sinQ θ * Crat i 0 + cosQ θ * Crat i 1,
                       Crat i 2] := by
  intro θ
  simp only [taylorVertex, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
    Int.reduceNeg, Matrix.smul_cons, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    smul_add, Matrix.smul_empty]
  ext i
  fin_cases i
  · simp [θ]
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, θ]
    ring
  · rfl
