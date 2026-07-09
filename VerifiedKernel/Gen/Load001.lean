import Noperthedron.SolutionTable.Load

/-! GENERATED (scripts/gen_kernel_chunks.py): rows [8192, 16384) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v6.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks "solution_tree_v6.csv" from 8192 to 16384 chunkSize 512

end Noperthedron.Solution
