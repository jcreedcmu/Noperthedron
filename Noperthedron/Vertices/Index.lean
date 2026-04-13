import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype

namespace Noperthedron

structure VertexIndex : Type where
  k : Fin 15
  ℓ : Fin 2
  i : Fin 3
deriving Fintype, DecidableEq, Repr

def VertexIndex.ofFin90 (j : Fin 90) : VertexIndex :=
 ⟨⟨j.val % 15, by omega⟩, ⟨j.val / 45, by omega⟩, ⟨(j.val % 45) / 15, by omega⟩⟩

instance instOfNatVertexIndexZero : OfNat VertexIndex 0 where
  ofNat := ⟨0, 0, 0⟩
