import Noperthedron.Final
import Noperthedron.MainTheorem

namespace Noperthedron

theorem valid_table_imples_exists_not_rupert (tab : Solution.ValidTable) :
    ExistsNonRupertPolyhedron := by
  use Noperthedron.exactVerts
  constructor
  · sorry
  · sorry

/-
Here we want to allow only [propext, Classical.choice, Quot.sound].
-/
#print axioms valid_table_imples_exists_not_rupert
