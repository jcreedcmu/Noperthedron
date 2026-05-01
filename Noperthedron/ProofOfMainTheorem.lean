import Noperthedron.MainTheorem

/-!
Proof of the main theorem. We expect this to take a long time (hours) to typecheck,
so we will need some way to hide it during routine builds.
-/

theorem exists_not_rupert : ExistsNonRupertPolyhedron := by
  sorry

/-
Here we foresee needing `Lean.trustCompiler` and/or `Lean.ofReduceBool`.
-/
#print axioms exists_not_rupert
