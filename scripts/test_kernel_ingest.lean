import Noperthedron.SolutionTable.KernelIngest

/-!
Smoke test for elaboration-time CSV ingestion + kernel-only row checking.
Run from the repo root (needs `solution_tree_v6.csv` unzipped there):

  lake env lean scripts/test_kernel_ingest.lean

Rows 8018–8022 include three global leaves (8018, 8020, 8022) and two
splits (vacuous here); row 1008268 is the first local leaf in the table.
-/

namespace Noperthedron.Solution

set_option Elab.async false

kernel_check_csv_rows "solution_tree_v6.csv" from 8018 to 8023

kernel_check_csv_rows "solution_tree_v6.csv" from 1008268 to 1008269

#print axioms csvRows_8018_8023_ok
#print axioms csvRows_1008268_1008269_ok

end Noperthedron.Solution
