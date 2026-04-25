import Noperthedron.Final
import Noperthedron.MainTheorem

namespace Noperthedron

theorem valid_table_imples_exists_not_rupert {tab : Solution.Table}
    (ht : tab.Valid)
    (hz : 0 < tab.size)
    (hi : (tightInterval : Set Pose) ⊆ (tab[0].interval : Set Pose)) :
    ExistsNotRupert := by
  sorry

/-
Here we want to allow only [propext, Classical.choice, Quot.sound].
-/
#print axioms valid_table_imples_exists_not_rupert
