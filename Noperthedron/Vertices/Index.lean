module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

namespace Noperthedron

@[expose] public section

/--
Identifier for a Noperthedron vertex.
Corresponds to the point at `(-1)^ℓ • Rz(2π k / 15) (C i)`
-/
structure VertexIndex : Type where
  k : Fin 15
  ℓ : Fin 2
  i : Fin 3
deriving Fintype, DecidableEq, Repr, Nonempty

end

end Noperthedron
