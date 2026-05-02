import Noperthedron.MainTheorem
import Noperthedron.Final
import Noperthedron.Vertices.InteriorNonempty

/-!
Proof of the main theorem. We expect this to take a long time (hours) to typecheck,
so we will need some way to hide it during routine builds.
-/

namespace Noperthedron

theorem exists_not_rupert : ExistsNonRupertPolyhedron := by
  obtain ⟨vtab⟩ := exists_solution_table
  exact ⟨Noperthedron.exactVerts, interior_exactVerts_hull_nonempty, nopert_not_rupert vtab⟩

/-
Here we foresee needing `Lean.trustCompiler` and/or `Lean.ofReduceBool`.
-/
#print axioms exists_not_rupert
