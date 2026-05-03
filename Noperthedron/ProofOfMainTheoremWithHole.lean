import Noperthedron.Final
import Noperthedron.MainTheorem
import Noperthedron.Vertices.InteriorNonempty

namespace Noperthedron

theorem valid_table_imples_exists_not_rupert (vtab : Solution.ValidTable) : ExistsNonRupertPolyhedron :=
  ⟨Noperthedron.exactVerts, interior_exactVerts_hull_nonempty, nopert_not_rupert vtab⟩

/--
info: 'Noperthedron.valid_table_imples_exists_not_rupert' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms valid_table_imples_exists_not_rupert
