import Noperthedron.Final
import Noperthedron.MainTheorem
import Noperthedron.Vertices.InteriorNonempty

namespace Noperthedron

theorem valid_table_imples_exists_not_rupert (vtab : Solution.ValidTable) : ExistsNonRupertPolyhedron :=
  ⟨Noperthedron.exactVerts, interior_exactVerts_hull_nonempty, nopert_not_rupert vtab⟩

/-
Here we want to allow only [propext, Classical.choice, Quot.sound].
-/
#print axioms valid_table_imples_exists_not_rupert
