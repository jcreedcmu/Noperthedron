#!/usr/bin/env python3
"""Regenerate Noperthedron/Vertices/PythonInt.lean from Vertices/Python.lean:
the same 810 vertex integers with the division by 10^16 dropped (mkV -> mkI),
plus a decide +kernel lemma certifying every entry against
pythonVertexCurried. Run from the repo root."""

src = open('Noperthedron/Vertices/Python.lean').read()
start = src.index('def pythonVertexCurried')
end = src.index('\n]', start) + 2
table = src[start:end]
table = table.replace(
    'def pythonVertexCurried : Fin 2 → Fin 3 → Fin 15 → Fin 3 → ℚ := ![',
    'def pythonVertexNumCurried : Fin 2 → Fin 3 → Fin 15 → Fin 3 → ℤ := ![')
table = table.replace('mkV ', 'mkI ')

out = f'''import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs

import Noperthedron.Vertices.Index
import Noperthedron.Vertices.Python

namespace Noperthedron

/-! ## Integer vertex data (scale `10¹⁶`)

GENERATED from `Vertices/Python.lean` (same integers, division by `10¹⁶`
dropped): the numerators of `pythonVertexCurried` as curried `![…]` literals,
for the integer-core checkers (`Checker/LocalNat.lean`), whose kernel
reductions read vertex coordinates as bare `ℤ` literals — a curried access
walks ≤ 25 `Fin.cons` cells and does no `ℚ` normalization.

`pythonVertexNumCurried_eq` certifies every entry against
`pythonVertexCurried`.

Regenerate with:
  python3 scripts/gen_python_int.py
-/

private def mkI (a b c : ℤ) : Fin 3 → ℤ :=
  fun | 0 => a | 1 => b | 2 => c

{table}

/-- Integer vertex numerators by `VertexIndex`. -/
def pythonVertexNum (idx : VertexIndex) : Fin 3 → ℤ :=
  pythonVertexNumCurried idx.ℓ idx.i idx.k

/-- Every integer entry is the scale-`10¹⁶` numerator of the rational one. -/
lemma pythonVertexNumCurried_eq :
    ∀ (ℓ : Fin 2) (i : Fin 3) (k : Fin 15) (c : Fin 3),
      pythonVertexCurried ℓ i k c = (pythonVertexNumCurried ℓ i k c : ℚ) / 10 ^ 16 := by
  decide +kernel

end Noperthedron
'''
open('Noperthedron/Vertices/PythonInt.lean', 'w').write(out)
print("wrote Noperthedron/Vertices/PythonInt.lean")
