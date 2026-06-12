import Noperthedron.Checker.RowZero
import Noperthedron.PoseInterval
import Noperthedron.SolutionTable
import Noperthedron.SolutionTable.Check
import Noperthedron.SolutionTable.Parse
import Noperthedron.Vertices.Exact

/-!
  Expensive computational step: `native_decide` parses the SY25 solution-tree
  CSV and checks every row of the resulting ~18.7-million-row table. The work
  is split into parallel tasks (see `Solution.checkSolutionCsv`), so on an
  N-core machine it runs roughly N× faster than the sequential check; expect
  it to take a few hours on 16 cores. Memory: the CSV is 2.5 GB and the parsed
  table is several times that, so a machine with ≳32 GB of RAM is recommended.

  `constructValidTable.lean` runs the same parse-and-check functions as a
  natively compiled executable, which is faster than the `native_decide`
  evaluation here (the interpreter executes the module's compiled IR but is
  slower than optimized native code). It is useful as a dry run.
-/

namespace Noperthedron

/-- The Steininger–Yurkevich solution tree, unzipped from
https://github.com/Jakob256/Rupert/blob/main/data/solution_tree.zip -/
def solution_csv : String :=
  include_str "../../noperthedron-verification-py/data/solution_tree.csv"

theorem exists_solution_table : ∃ (tab : Solution.ValidTable), True := by
  have h : Solution.checkSolutionCsv solution_csv 64 512 = true := by native_decide
  exact Solution.checkSolutionCsv_sound h
