import Noperthedron.SolutionTable.KernelIngest

/-! Scale test: one 100-row chunk (mostly global leaves), then the same
number of rows as four 25-row chunks, to compare amortization and check
that kernel memory is freed between declarations. -/

namespace Noperthedron.Solution

set_option Elab.async false

kernel_check_csv_rows "solution_tree_v6.csv" from 8018 to 8118

kernel_check_csv_rows "solution_tree_v6.csv" from 8118 to 8143
kernel_check_csv_rows "solution_tree_v6.csv" from 8143 to 8168
kernel_check_csv_rows "solution_tree_v6.csv" from 8168 to 8193
kernel_check_csv_rows "solution_tree_v6.csv" from 8193 to 8218

end Noperthedron.Solution
