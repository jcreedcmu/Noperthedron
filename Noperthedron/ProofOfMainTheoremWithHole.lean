import Noperthedron.Final
import Noperthedron.MainTheorem

namespace Noperthedron

theorem valid_table_imples_exists_not_rupert (vtab : Solution.ValidTable) :
    ExistsNonRupertPolyhedron := by
  use Noperthedron.exactVerts
  constructor
  · sorry
  · exact nopert_not_rupert vtab

/-
Here we want to allow only [propext, Classical.choice, Quot.sound].
-/
#print axioms valid_table_imples_exists_not_rupert
