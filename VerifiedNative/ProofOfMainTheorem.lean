import Noperthedron.ProofOfMainTheoremWithHole
import VerifiedNative.ComputationalStep

/-!
Proof of the main theorem, with the solution table actually verified
(by `native_decide`; see `VerifiedNative/ComputationalStep.lean`).
-/

namespace Noperthedron.Verified.Native

open Noperthedron

/--
  There exists a convex polyhedron that does not have the Rupert property.
-/
theorem exists_not_rupert : ExistsNonRupertPolyhedron :=
  valid_table_imples_exists_not_rupert exists_solution_table.choose

/- Expected: `propext`, `Classical.choice`, `Quot.sound`, and the two
`native_decide` axiom instances — no `sorryAx`. -/
#print axioms exists_not_rupert

end Noperthedron.Verified.Native
