import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
This file states our main theorem using only Mathlib imports, following the conventions
proposed on Zulip here:
https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs/near/556956066

See also the Formal Conjectures version of the theorem statement:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/Rupert.lean
-/

/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def proj_xy {k : Type} (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  !₂[v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as a finite set of vertices. -/
def IsRupert (vertices : Finset (EuclideanSpace ℝ (Fin 3))) : Prop :=
   ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
   ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   let hull := convexHull ℝ vertices
   let inner_shadow := { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ hull }
   let outer_shadow := { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow

/--
The main result we want to prove: there exists a convex polyhedron (represented as
a finite set of vertices) that does not have the Rupert Property.
-/
def ExistsNotRupert : Prop :=
  ∃ vs : Finset (EuclideanSpace ℝ (Fin 3)),
    (interior (convexHull ℝ vs : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty ∧
    ¬IsRupert vs
