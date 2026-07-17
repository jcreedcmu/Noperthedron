module

public import Noperthedron.SolutionTable.Load
public meta import Noperthedron.SolutionTable.Load

@[expose] public section


/-! GENERATED (scripts/gen_kernel_chunks.py): rows [1335296, 1343488) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v6.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks_curried "solution_tree_v6.csv" from 1335296 to 1343488 chunkSize 512

end Noperthedron.Solution

end
