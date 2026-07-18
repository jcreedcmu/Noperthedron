module

public import Noperthedron.MainTheorem
public import Noperthedron.NoperthedronIsNotRupert
public import Noperthedron.Vertices.InteriorNonempty

public section


namespace Noperthedron

/--
The existence of a well-formed `Solution.ValidTable` object implies the existence
of a convex polyhedron that does not have the Rupert Property.
-/
theorem valid_table_implies_exists_not_rupert (vtab : Solution.ValidTable) : ExistsNonRupertPolyhedron :=
  ⟨Noperthedron.exactVerts, interior_exactVerts_hull_nonempty, nopert_not_rupert vtab⟩

/--
info: 'Noperthedron.valid_table_implies_exists_not_rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms valid_table_implies_exists_not_rupert

end Noperthedron
end
