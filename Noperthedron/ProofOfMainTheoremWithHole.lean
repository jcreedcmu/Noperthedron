import Noperthedron.Final
import Noperthedron.MainTheorem

namespace Noperthedron

theorem valid_table_imples_exists_not_rupert {tab : Solution.Table}
    (ht : tab.RowsValid)
    (hz : 0 < tab.size)
    (hi : (tightInterval : Set (Pose ℝ)) ⊆ (tab[0].interval : Set (Pose ℝ))) :
    ExistsNonRupertPolyhedron := by
  use Noperthedron.exactVerts
  constructor
  · sorry
  · sorry

/-
Here we want to allow only [propext, Classical.choice, Quot.sound].
-/
#print axioms valid_table_imples_exists_not_rupert
