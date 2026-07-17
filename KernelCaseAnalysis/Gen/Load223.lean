module

public import Noperthedron.SolutionTable.Load
public meta import Noperthedron.SolutionTable.Load

@[expose] public section


/-! GENERATED (scripts/gen_kernel_chunks.py): rows [1826816, 1835008) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v6.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks_curried "solution_tree_v6.csv" from 1826816 to 1835008 chunkSize 512

end Noperthedron.Solution

end
