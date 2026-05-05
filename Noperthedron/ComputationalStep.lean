import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.Vertices.Exact

namespace Noperthedron

--def csv : String := include_str "../../noperthedron-verification-py/data/solution_tree.csv"

theorem exists_solution_table : ∃ (tab : Solution.ValidTable), True
     := by
  sorry -- TODO(hard)
