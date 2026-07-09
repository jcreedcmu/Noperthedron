import Noperthedron.SolutionTable.Load

/-! GENERATED (scripts/gen_kernel_chunks.py): rows [65536, 73728) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v6.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks "solution_tree_v6.csv" from 65536 to 73728 chunkSize 512

end Noperthedron.Solution
