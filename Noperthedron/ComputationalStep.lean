import Noperthedron.Checker.RowZero
import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.SolutionTable.Check
import Noperthedron.SolutionTable.Parse
import Noperthedron.Vertices.Exact

/-!
  Expensive computational step: `native_decide` parses the solution-tree CSV
  and checks every row of the resulting ~2.05-million-row table (the v6 tree,
  regenerated from scratch with the anisotropic second-order certificate;
  9.1x fewer rows than the original). It would potentially go faster if we set
  `precompiledModules = true`.

  The full check is commented out so that it doesn't bog down compilation
  as we work on the rest of the project. It takes about 25 minutes on a 16-core
  machine.

  To run the same check in a standalone native executable, try
  `constructValidTable.lean`, which takes about 5 minutes on a 16-core
  machine.
-/

namespace Noperthedron

/-- An optimized version of the Steininger–Yurkevich solution tree,
downloaded from git-lfs and unzipped. -/
def solution_csv : String :=
  -- Uncomment the following line and point it to the file's location.
  -- include_str "../solution_tree_v6.csv"
  sorry

theorem exists_solution_table : ∃ (_ : Solution.ValidTable), True := by
  have h : Solution.checkSolutionCsv solution_csv 64 512 = true := by
    -- Uncomment the following step.
    -- native_decide
    sorry
  exact Solution.checkSolutionCsv_sound h
