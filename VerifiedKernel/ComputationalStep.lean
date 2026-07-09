import Noperthedron.SolutionTable.Assemble
import VerifiedKernel.Gen.Final

/-!
# The expensive computational step, verified kernel-only

Builds the `ValidTable` from the generated chunk tree: the 2,051,521 rows
are loaded as literal 512-row chunks (`Gen/LoadNNN.lean`), served through
the digit-curried getter (`Gen/Dispatch.lean`), validated range-by-range
with `decide +kernel` (`Gen/ValidateNNNN.lean` — the expensive part), and
folded by the `RangeOk` combine chain (`Gen/CombineNN.lean`, `Gen/Final.lean`).

Everything here is checked by the Lean kernel alone: axioms are `propext`,
`Classical.choice`, and `Quot.sound` — no `sorry`, no `ofReduceBool`.

This library is deliberately **not** in `defaultTargets`: building it is the
full kernel verification run (~150 core-hours; RAM-bound to about 5-way
parallelism — expect ~30 hours wall on a 10-core/32 GB machine):

    lake build VerifiedKernel
-/

namespace Noperthedron.Verified.Kernel

open Noperthedron Noperthedron.Solution

theorem exists_solution_table : ∃ (_ : Solution.ValidTable), True :=
  ⟨Solution.validTableOfGetter getRow 2051521 (by norm_num)
      row0_interval allRows_validIxAt,
    trivial⟩

end Noperthedron.Verified.Kernel
