import Noperthedron.SolutionTable.Assemble
import Noperthedron.SolutionTable.Parse

/-!
# The expensive computational step, verified with `native_decide`

This library is deliberately **not** in `defaultTargets`, so the default
build and CI never pay for it. Build it on demand (about 25 minutes on 16
cores), with `solution_tree_v6.csv` unzipped at the repo root:

    lake build VerifiedNative

It parses the solution-tree CSV (untrusted, in 64 parallel tasks) and checks
every one of the 2,051,521 rows with `native_decide` via the getter-based
statement machinery of `SolutionTable/Assemble.lean` — the same statements
the kernel-only route (`VerifiedKernel`) proves chunk-by-chunk over
literal-encoded rows.
-/

namespace Noperthedron.Verified.Native

open Noperthedron

/-- The Steininger–Yurkevich solution tree (v6), embedded at elaboration
time. -/
def solution_csv : String := include_str "../solution_tree_v6.csv"

/-- The number of rows in the solution tree. -/
def solutionRows : ℕ := 2051521

/-- The solution table, parsed from the CSV (empty on parse failure, in which
case the validity check below simply fails: nothing about the parse is
trusted). -/
def solutionTable : Solution.Table :=
  match Solution.parseSolutionTablePar solution_csv 64 with
  | .ok t => t
  | .error _ => #[]

/-- Row getter backing the validity statements. -/
def solutionGetRow (i : ℕ) : Solution.Row := solutionTable[i]!

theorem solution_row0_interval :
    (solutionGetRow 0).interval = Solution.rowZero.interval := by
  native_decide

theorem solution_rows_valid :
    Solution.rowsValidIxAtParB solutionGetRow solutionRows 512 = true := by
  native_decide

theorem exists_solution_table : ∃ (_ : Solution.ValidTable), True :=
  ⟨Solution.validTableOfGetter solutionGetRow solutionRows
      (by norm_num [solutionRows])
      solution_row0_interval
      (Solution.validIxAt_of_rowsValidIxAtParB solution_rows_valid),
    trivial⟩

end Noperthedron.Verified.Native
