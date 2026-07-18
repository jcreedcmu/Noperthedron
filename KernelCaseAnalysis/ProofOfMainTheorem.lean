module

public import Noperthedron.ProofOfMainTheoremWithHole
public import KernelCaseAnalysis.ComputationalStep

@[expose] public section


/-!
Proof of the main theorem, with the solution table verified by the Lean
kernel alone (see `KernelCaseAnalysis/ComputationalStep.lean`).
-/

namespace Noperthedron.KernelCaseAnalysis

open Noperthedron

/--
  There exists a convex polyhedron that does not have the Rupert property.
-/
theorem exists_not_rupert : ExistsNonRupertPolyhedron :=
  valid_table_implies_exists_not_rupert solutionTable

/- Expected: `propext`, `Classical.choice`, `Quot.sound` — nothing else. -/
#print axioms exists_not_rupert

end Noperthedron.KernelCaseAnalysis

end
