import Noperthedron.SolutionTable.Load

/-! Experiment: can `native_decide` consume loaded chunks? This requires the
code generator to handle chunk-literal definitions (`compiled` flag). -/

namespace Noperthedron.Solution

load_csv_rows "solution_tree_v6.csv" from 8018 to 8023 compiled

theorem csvRows_8018_8023_leafOk_native :
    csvRows_8018_8023.all Row.leafOk = true := by
  native_decide

#print axioms csvRows_8018_8023_leafOk_native

/- Larger chunk, to see whether codegen scales. -/
load_csv_rows "solution_tree_v6.csv" from 8018 to 8530 compiled

theorem csvRows_8018_8530_leafOk_native :
    csvRows_8018_8530.all Row.leafOk = true := by
  native_decide

end Noperthedron.Solution
