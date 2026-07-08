import Noperthedron.SolutionTable.Assemble
import Noperthedron.SolutionTable.Parse

/-!
# The expensive computational step, verified with `native_decide`

This library is deliberately **not** in `defaultTargets`, so the default
build and CI never pay for it. Build it on demand (tens of minutes), with
`solution_tree_v6.csv` unzipped at the repo root:

    lake build VerifiedNative

It parses the solution-tree CSV (untrusted, in 64 parallel tasks) and checks
every one of the 2,051,521 rows with one `native_decide` via the getter-based
statement machinery of `SolutionTable/Assemble.lean` — the same statements
the kernel-only route (`VerifiedKernel`) proves chunk-by-chunk over
literal-encoded rows.

Note the shape of `checkSolution`: the parsed table must be bound *inside*
the decided expression. Binding it as a top-level `def` instead deadlocks
under `native_decide`'s interpreter — the `Task.spawn`ed row-checking
closures all block on the lazy initialization of the constant (measured:
0% CPU, no progress), whereas the `match`-bound local is evaluated exactly
once before the tasks fan out.
-/

namespace Noperthedron.Verified.Native

open Noperthedron

/-- The Steininger–Yurkevich solution tree (v6), embedded at elaboration
time. -/
def solution_csv : String := include_str "../solution_tree_v6.csv"

/-- The number of rows in the solution tree. -/
def solutionRows : ℕ := 2051521

/-- Parse the CSV (in 64 parallel tasks) and check, in `nTasks` parallel
tasks, that row 0 carries `rowZero.interval` and that every index below `n`
satisfies `Row.ValidIxAt` for the parsed-table row getter. Nothing about the
parse is trusted: on failure the check is simply `false`. -/
def checkSolution (csv : String) (n nTasks : ℕ) : Bool :=
  match Solution.parseSolutionTablePar csv 64 with
  | .error _ => false
  | .ok tab =>
    decide ((tab[0]!).interval = Solution.rowZero.interval) &&
    Solution.rowsValidIxAtParB (fun i => tab[i]!) n nTasks

theorem solution_checked : checkSolution solution_csv solutionRows 512 = true := by
  native_decide

theorem exists_solution_table : ∃ (_ : Solution.ValidTable), True := by
  have h := solution_checked
  unfold checkSolution at h
  split at h
  · exact absurd h (by simp)
  · rw [Bool.and_eq_true, decide_eq_true_iff] at h
    exact ⟨Solution.validTableOfGetter _ solutionRows (by norm_num [solutionRows])
        h.1 (Solution.validIxAt_of_rowsValidIxAtParB h.2),
      trivial⟩

end Noperthedron.Verified.Native
