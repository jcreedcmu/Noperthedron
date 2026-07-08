import Noperthedron.SolutionTable.Load

/-! Scale test: one 100-row chunk (mostly global leaves), then the same
number of rows as four 25-row chunks, to compare amortization and check
that kernel memory is freed between declarations. -/

namespace Noperthedron.Solution

set_option Elab.async false

load_csv_rows "solution_tree_v6.csv" from 8018 to 8118

theorem csvRows_8018_8118_leafOk : csvRows_8018_8118.all Row.leafOk = true := by
  decide +kernel

load_csv_rows "solution_tree_v6.csv" from 8118 to 8143
load_csv_rows "solution_tree_v6.csv" from 8143 to 8168
load_csv_rows "solution_tree_v6.csv" from 8168 to 8193
load_csv_rows "solution_tree_v6.csv" from 8193 to 8218

theorem csvRows_8118_8143_leafOk : csvRows_8118_8143.all Row.leafOk = true := by
  decide +kernel
theorem csvRows_8143_8168_leafOk : csvRows_8143_8168.all Row.leafOk = true := by
  decide +kernel
theorem csvRows_8168_8193_leafOk : csvRows_8168_8193.all Row.leafOk = true := by
  decide +kernel
theorem csvRows_8193_8218_leafOk : csvRows_8193_8218.all Row.leafOk = true := by
  decide +kernel

end Noperthedron.Solution
