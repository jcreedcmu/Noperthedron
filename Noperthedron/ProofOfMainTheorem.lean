import Noperthedron.MainTheorem
import Noperthedron.NoperthedronIsNotRupert
import Noperthedron.Vertices.InteriorNonempty

/-!
Proof of the main theorem.
-/

namespace Noperthedron

/--
  There exists a convex polyhedron that does not have the Rupert property.
-/
theorem exists_not_rupert : ExistsNonRupertPolyhedron := by
  obtain ⟨vtab⟩ := exists_solution_table
  exact ⟨Noperthedron.exactVerts, interior_exactVerts_hull_nonempty, nopert_not_rupert vtab⟩

/-
Here we foresee needing `Lean.trustCompiler` and/or `Lean.ofReduceBool`.
-/
#print axioms exists_not_rupert
