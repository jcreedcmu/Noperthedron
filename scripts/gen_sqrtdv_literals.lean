import Noperthedron.Checker.ApproxSqrt
import Noperthedron.Vertices.Python

/-!
Generator for `Noperthedron/Checker/SqrtDvLiterals.lean`: the 90 × 90 pairwise
`upper_sqrt` vertex-difference norms as source-literal rationals, in curried
`![…]` form (kernel-friendly), together with `decide +kernel` lemmas proving
each entry equal to `sqrtApprox.upper_sqrt.norm (pythonVertexA a - pythonVertexA b)`.

Regenerate with:

  lake env lean --run scripts/gen_sqrtdv_literals.lean > Noperthedron/Checker/SqrtDvLiterals.lean
-/

open Noperthedron RationalApprox

private def entry (ℓa : Fin 2) (ia : Fin 3) (ka : Fin 15)
    (ℓb : Fin 2) (ib : Fin 3) (kb : Fin 15) : ℚ :=
  sqrtApprox.upper_sqrt.norm (pythonVertexA ⟨ka, ℓa, ia⟩ - pythonVertexA ⟨kb, ℓb, ib⟩)

private def fmtQ (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

private def fins (n : ℕ) : List (Fin (n + 1)) := List.finRange (n + 1)

/-- Innermost row: the 15 values over `kb`, on one line. -/
private def rowKb (ℓa : Fin 2) (ia : Fin 3) (ka : Fin 15) (ℓb : Fin 2) (ib : Fin 3) :
    String :=
  "![" ++ ", ".intercalate ((fins 14).map fun kb => fmtQ (entry ℓa ia ka ℓb ib kb)) ++ "]"

private def blockIb (ℓa : Fin 2) (ia : Fin 3) (ka : Fin 15) (ℓb : Fin 2) : String :=
  "![" ++ ",\n      ".intercalate ((fins 2).map (rowKb ℓa ia ka ℓb)) ++ "]"

private def blockLb (ℓa : Fin 2) (ia : Fin 3) (ka : Fin 15) : String :=
  s!"-- a = ⟨{ka}, {ℓa}, {ia}⟩\n    ![" ++
    ",\n     ".intercalate ((fins 1).map (blockIb ℓa ia ka)) ++ "]"

private def blockKa (ℓa : Fin 2) (ia : Fin 3) : String :=
  "![" ++ ",\n    ".intercalate ((fins 14).map (blockLb ℓa ia)) ++ "]"

private def blockIa (ℓa : Fin 2) : String :=
  "![" ++ ",\n   ".intercalate ((fins 2).map (blockKa ℓa)) ++ "]"

private def table : String :=
  "![" ++ ",\n  ".intercalate ((fins 1).map blockIa) ++ "]"

private def chunkLemma (ℓ : Fin 2) (i : Fin 3) : String :=
  s!"private lemma sqrtDvCurried_eq_{ℓ}_{i} : ∀ (k : Fin 15) (b : VertexIndex),
    sqrtDvCurried {ℓ} {i} k b.ℓ b.i b.k
      = RationalApprox.sqrtApprox.upper_sqrt.norm
          (pythonVertexA ⟨k, {ℓ}, {i}⟩ - pythonVertexA b) := by
  decide +kernel
"

private def header : String :=
"/-
GENERATED FILE — do not edit by hand.

Regenerate with:
  lake env lean --run scripts/gen_sqrtdv_literals.lean > Noperthedron/Checker/SqrtDvLiterals.lean
-/
import Mathlib.Tactic.FinCases

import Noperthedron.Checker.ApproxSqrt
import Noperthedron.Vertices.Python

/-!
# Pairwise vertex-difference norms, as source literals

All 90 × 90 values `sqrtApprox.upper_sqrt.norm (pythonVertexA a - pythonVertexA b)`,
stored as literal rationals in curried `![…]` (`Fin.cons`) form, indexed by the
`VertexIndex` components of `a` and `b` as `(a.ℓ, a.i, a.k, b.ℓ, b.i, b.k)`.

The local checker's hot loop reads these values through `sqrtDv`
(see `Noperthedron/Checker/Local.lean`). A curried literal — unlike the
`Array.ofFn` table it replaces — is cheap for the *kernel* to read: an access
walks at most 40 `Fin.cons` cells, whereas reducing an 8100-entry
`Array.push` chain made a single high-index access cost tens of gigabytes
under `decide +kernel`.

`sqrtDvCurried_eq` certifies every entry against the defining formula; it is
proved by six `decide +kernel` chunks (one per `(a.ℓ, a.i)`, 1350 square
roots each) to bound kernel memory.
-/

namespace Noperthedron.Solution
"

private def combined : String :=
"/-- Each literal in `sqrtDvCurried` equals the `upper_sqrt` norm of the
corresponding vertex difference. -/
lemma sqrtDvCurried_eq (a b : VertexIndex) :
    sqrtDvCurried a.ℓ a.i a.k b.ℓ b.i b.k
      = RationalApprox.sqrtApprox.upper_sqrt.norm
          (pythonVertexA a - pythonVertexA b) := by
  obtain ⟨k, ℓ, i⟩ := a
  fin_cases ℓ <;> fin_cases i
  · exact sqrtDvCurried_eq_0_0 k b
  · exact sqrtDvCurried_eq_0_1 k b
  · exact sqrtDvCurried_eq_0_2 k b
  · exact sqrtDvCurried_eq_1_0 k b
  · exact sqrtDvCurried_eq_1_1 k b
  · exact sqrtDvCurried_eq_1_2 k b

end Noperthedron.Solution"

def main : IO Unit := do
  let mut out := header ++ "\n"
  out := out ++ "set_option maxRecDepth 16384 in\n"
  out := out ++ "/-- All 90 × 90 pairwise `upper_sqrt` vertex-difference norms as literals,\n"
  out := out ++ "indexed by `(a.ℓ, a.i, a.k, b.ℓ, b.i, b.k)`. -/\n"
  out := out ++ "def sqrtDvCurried : Fin 2 → Fin 3 → Fin 15 → Fin 2 → Fin 3 → Fin 15 → ℚ :=\n"
  out := out ++ table ++ "\n\n"
  for ℓ in fins 1 do
    for i in fins 2 do
      out := out ++ chunkLemma ℓ i ++ "\n"
  out := out ++ combined
  IO.println out
