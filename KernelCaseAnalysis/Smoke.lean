import Noperthedron.SolutionTable.Assemble
import Noperthedron.SolutionTable.Load

/-!
# Kernel-pipeline smoke test

A small-scale, end-to-end exercise of the kernel-only verification pipeline
on real solution-table rows, so that `lake build KernelCaseAnalysis` actually
runs `decide +kernel` checks today (about half a minute; requires
`solution_tree_v6.csv` unzipped at the repo root):

* `load_csv_rows` loads rows as literal `Row` definitions (elaboration-time
  parsing, no kernel string processing);
* leaf checks (`Row.leafOk`): three global leaves and one local leaf;
* split checks through the exact production pipeline
  (`load_csv_chunks_curried` / `assemble_row_dispatch_curried` /
  `rowGetterC`) — `Row.ValidIxAt`, the statement shape the full run proves
  range-by-range via `RangeOk`;
* `#guard_msgs` pins every theorem to the three standard axioms — the build
  fails if `sorryAx` or `ofReduceBool` ever sneaks in.
-/

namespace Noperthedron.KernelCaseAnalysis.Smoke

open Noperthedron.Solution

/-! ### Leaf validation
Rows 8018–8022 contain three global leaves (8018, 8020, 8022) and two splits
(vacuous for `Row.leafOk`); row 1008268 is the first local leaf in the table. -/

load_csv_rows "solution_tree_v6.csv" from 8018 to 8023

theorem csvRows_8018_8023_leafOk : csvRows_8018_8023.all Row.leafOk = true := by
  decide +kernel

load_csv_rows "solution_tree_v6.csv" from 1008268 to 1008269

theorem csvRows_1008268_1008269_leafOk :
    csvRows_1008268_1008269.all Row.leafOk = true := by
  decide +kernel

/-! ### Split validation through the getter
The first 16 rows of the tree are all splits whose children (up to row 168)
lie inside the first 512 rows, so a getter over the loaded prefix suffices.
`Row.ValidIxAt` is the statement the full run proves for every index, and
the curried loader/dispatch/getter chain is exactly the one the generated
`Gen/` files use. -/

load_csv_chunks_curried "solution_tree_v6.csv" from 0 to 512 chunkSize 512

assemble_row_dispatch_curried prefixDispatch rows 512 chunkSize 512

noncomputable def getPrefix : ℕ → Row := rowGetterC prefixDispatch

theorem prefix_row0_interval : (getPrefix 0).interval = rowZero.interval := by
  decide +kernel

theorem prefix_first_splits_validIx :
    ∀ j : Fin 16, Row.ValidIxAt getPrefix 512 j.val := by
  decide +kernel

/-! ### Axiom guards: the standard three only — no `ofReduceBool`, no `sorryAx`. -/

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.csvRows_8018_8023_leafOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms csvRows_8018_8023_leafOk

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.csvRows_1008268_1008269_leafOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms csvRows_1008268_1008269_leafOk

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.prefix_row0_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_row0_interval

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.prefix_first_splits_validIx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prefix_first_splits_validIx

end Noperthedron.KernelCaseAnalysis.Smoke
