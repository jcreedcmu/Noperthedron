import Noperthedron.Checker.RowZero
import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.SolutionTable.Check
import Noperthedron.SolutionTable.Parse
import Noperthedron.Vertices.Exact

/-!
  Expensive computational step: `native_decide` parses the SY25 solution-tree
  CSV and checks every row of the resulting ~18.7-million-row table. On a 16
  core machine, this takes about 30 hours and consumes about 55 GB of memory.
  It would potentially go faster if we set `precompiledModules = true`.

  The full check is commented out so that it doesn't bog down compilation
  as we work on the rest of the project.

  To run the same check in a standalone native executable, try
  `constructValidTable.lean`, which should take about 2.5 hours on a 16-core
  machine.
-/

namespace Noperthedron

/-- The Steininger–Yurkevich solution tree, unzipped from
https://github.com/Jakob256/Rupert/blob/main/data/solution_tree.zip -/
def solution_csv : String :=
  -- Uncomment the following line and point it to the file's location.
  -- include_str "../../noperthedron-verification-py/data/solution_tree.csv"
  sorry

theorem exists_solution_table : ∃ (_ : Solution.ValidTable), True := by
  have h : Solution.checkSolutionCsv solution_csv 64 512 = true := by
    -- Uncomment the following step.
    -- native_decide
    sorry
  exact Solution.checkSolutionCsv_sound h
