import Noperthedron.SolutionTable.Load

/-!
Smoke test for elaboration-time CSV loading + kernel-only validation.
Run from the repo root (needs `solution_tree_v6.csv` unzipped there):

  lake env lean scripts/test_csv_load.lean

`load_csv_rows` only *loads* rows as literal definitions; every check below
is an ordinary theorem about the loaded chunk, proved by `decide +kernel`, so
the kernel does all the evaluation.
-/

namespace Noperthedron.Solution

set_option Elab.async false

/-! ### Leaf validation
Rows 8018–8022 contain three global leaves (8018, 8020, 8022) and two splits
(vacuous for `Row.leafOk`); row 1008268 is the first local leaf in the table. -/

load_csv_rows "solution_tree_v6.csv" from 8018 to 8023

theorem csvRows_8018_8023_leafOk : csvRows_8018_8023.all Row.leafOk = true := by
  decide +kernel

load_csv_rows "solution_tree_v6.csv" from 1008268 to 1008269

theorem csvRows_1008268_1008269_leafOk :
    csvRows_1008268_1008269.all Row.leafOk = true := by
  decide +kernel

/-! ### Split validation
Split rows are checked against a table view. The first 16 rows of the tree are
all splits whose children (up to row 168) lie inside the first 512 rows, so a
mini-table of the loaded prefix suffices; the full run will use the same
statement shape against a whole-table view. -/

load_csv_rows "solution_tree_v6.csv" from 0 to 512

noncomputable def miniTab : Table := csvRows_0_512.toArray

theorem first_splits_ok :
    ((csvRows_0_512.take 16).all fun r => decide (r.ValidSplit miniTab)) = true := by
  decide +kernel

/-! All three theorems use only the standard axioms — no `ofReduceBool`. -/

#print axioms csvRows_8018_8023_leafOk
#print axioms csvRows_1008268_1008269_leafOk
#print axioms first_splits_ok

end Noperthedron.Solution
