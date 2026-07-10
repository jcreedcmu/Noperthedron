import Noperthedron.SolutionTable.Load

/-! GENERATED (scripts/gen_kernel_chunks.py): rows [32768, 40960) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v6.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks_curried "solution_tree_v6.csv" from 32768 to 40960 chunkSize 512

end Noperthedron.Solution
