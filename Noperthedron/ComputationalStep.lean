import Noperthedron.Checker.RowZero
import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.SolutionTable.Check
import Noperthedron.SolutionTable.Parse
import Noperthedron.Vertices.Exact

/-!
  Expensive computational step: `native_decide` parses the solution-tree CSV
  and checks every row of the resulting ~5.6-million-row table (the v5 tree,
  regenerated from SY25's with the second-order certificate; 3.33x fewer rows
  than the original). It would potentially go faster if we set
  `precompiledModules = true`.

  The full check is commented out so that it doesn't bog down compilation
  as we work on the rest of the project.

  To run the same check in a standalone native executable, try
  `constructValidTable.lean`, which takes about 60 minutes on a 16-core
  machine.
-/

namespace Noperthedron

/-- An optimized version of the Steininger–Yurkevich solution tree,
downloaded from git-lfs and unzipped. -/
def solution_csv : String :=
  -- Uncomment the following line and point it to the file's location.
  -- include_str "../solution_tree_v5.csv"
  sorry

theorem exists_solution_table : ∃ (_ : Solution.ValidTable), True := by
  have h : Solution.checkSolutionCsv solution_csv 64 512 = true := by
    -- Uncomment the following step.
    -- native_decide
    sorry
  exact Solution.checkSolutionCsv_sound h
