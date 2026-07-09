import Noperthedron.ProofOfMainTheoremWithHole
import VerifiedKernel.ComputationalStep

/-!
Proof of the main theorem, with the solution table verified by the Lean
kernel alone (see `VerifiedKernel/ComputationalStep.lean`).
-/

namespace Noperthedron.Verified.Kernel

open Noperthedron

/--
  There exists a convex polyhedron that does not have the Rupert property.
-/
theorem exists_not_rupert : ExistsNonRupertPolyhedron :=
  valid_table_imples_exists_not_rupert exists_solution_table.choose

/- Expected: `propext`, `Classical.choice`, `Quot.sound` — nothing else. -/
#print axioms exists_not_rupert

end Noperthedron.Verified.Kernel
