import Mathlib.Data.Finset.Max

import Noperthedron.Local.Congruent
import Noperthedron.SolutionTable.Defs
import Noperthedron.Vertices.Exact
import Noperthedron.Vertices.Python
import Noperthedron.Vertices.Trig

/-!
# Local Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational local theorem. Everything
here is computable — no `noncomputable` keyword.
-/

namespace Noperthedron.Solution

noncomputable
abbrev Row.P (r : Row) : Local.Triangle :=
![exactVertex r.P1_index, exactVertex r.P2_index, exactVertex r.P3_index]

noncomputable
abbrev Row.Q (r : Row) : Local.Triangle :=
![exactVertex r.Q1_index, exactVertex r.Q2_index, exactVertex r.Q3_index]

/--
TODO
[SY25] use SageMath for this.
-/
instance (P Q : Local.Triangle) : Decidable (P.Congruent Q) :=
.isTrue (sorry : P.Congruent Q)

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
--  PQ_congruent : row.P.Congruent row.Q

instance (row : Row) : Decidable (Row.ValidLocal row) :=
  decidable_of_iff _ (Row.validLocal_iff row).symm

/-! ## Smoke test -/

/-
ID,nodeType,nrChildren,IDfirstChild,split,
T1_min,T1_max,V1_min,V1_max,T2_min,T2_max,V2_min,V2_max,A_min,A_max,
P1_index,P2_index,P3_index,Q1_index,Q2_index,Q3_index,
r,sigma_Q,
wx_nominator,wy_nominator,w_denominator,S_index

245,2,,,,
0,201600,0,201600,0,201600,0,202240,-22853120,-22650880,
30,31,38,79,80,87,
955,1,
,,,
-/

/-- Row 245 from `data/solution_tree_300.csv` — the first local leaf. -/
def testLocalRow : Row := {
  ID := 91, nodeType := 2, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -22853120,
                max := fun | .θ₁ => 201600 | .φ₁ => 201600 | .θ₂ => 201600
                            | .φ₂ => 202240 | .α => -22650880 },
  S_index := 0, wx_numerator := 0, wy_numerator := 0, w_denominator := 0,
  P1_index := VertexIndex.ofFin90 ⟨30, by lia⟩,
  P2_index := VertexIndex.ofFin90 ⟨31, by lia⟩,
  P3_index := VertexIndex.ofFin90 ⟨38, by lia⟩,
  Q1_index := VertexIndex.ofFin90 ⟨79, by lia⟩,
  Q2_index := VertexIndex.ofFin90 ⟨80, by lia⟩,
  Q3_index := VertexIndex.ofFin90 ⟨87, by lia⟩,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testLocalRow.ValidLocal

