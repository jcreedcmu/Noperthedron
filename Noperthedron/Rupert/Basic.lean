import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.EuclideanSpaceNotation

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def proj_xy {k : Type} (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  !₂[v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as a finite set of vertices. -/
def IsRupert (vertices : Finset ℝ³) : Prop :=
   ∃ inner_rotation ∈ SO3, ∃ inner_offset : ℝ², ∃ outer_rotation ∈ SO3,
   let hull := convexHull ℝ vertices
   let inner_shadow := { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ hull }
   let outer_shadow := { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow
