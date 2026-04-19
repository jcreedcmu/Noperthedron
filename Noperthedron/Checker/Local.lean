import Mathlib.Data.Finset.Max

import Noperthedron.SolutionTable.Defs
import Noperthedron.Vertices.Python
import Noperthedron.Vertices.Trig

/-!
# Local Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational local theorem. Everything
here is computable — no `noncomputable` keyword.
-/

namespace Noperthedron.Solution

/-- Assertion that a row constitutes a valid application of the rational global theorem. -/
@[mk_iff]
structure Row.ValidLocal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 2
  θ₁_lb : -4 ≤ row.θ₁
  θ₁_ub : row.θ₁ ≤ 4
  φ₁_lb : -4 ≤ row.φ₁
  φ₁_ub : row.φ₁ ≤ 4
  θ₂_lb : -4 ≤ row.θ₂
  θ₂_ub : row.θ₂ ≤ 4
  φ₂_lb : -4 ≤ row.φ₂
  φ₂_ub : row.φ₂ ≤ 4
  α_lb : -4 ≤ row.α
  α_ub : row.α ≤ 4

instance (row : Row) : Decidable (Row.ValidLocal row) :=
  decidable_of_iff _ (Row.validLocal_iff row).symm

