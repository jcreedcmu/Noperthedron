import Noperthedron.SolutionTable.Assemble
import Noperthedron.SolutionTable.Load

/-!
# The expensive computational step, verified kernel-only (placeholder)

This library will hold the kernel-only verification of the solution table:
generated modules that `load_csv_rows` the 2,051,521 rows as literal-encoded
chunks, a digit-curried row getter (`assemble_row_dispatch` / `rowGetter`),
per-chunk `ChunkOk … := by decide +kernel` theorems, and the `ChunkOkBelow`
combine chain, culminating in an `exists_solution_table` with axioms
`propext`, `Classical.choice`, `Quot.sound` only — the same statements
`VerifiedNative` proves with `native_decide`, but with the compiler removed
from the trusted base.

The generator and the ~400-core-hour build are still to come; see
`kernel-decide-note.md` and `Noperthedron/SolutionTable/Assemble.lean`.
-/
