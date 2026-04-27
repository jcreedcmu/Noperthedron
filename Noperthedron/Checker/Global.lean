import Mathlib.Data.Finset.Max

import Noperthedron.SolutionTable.Defs
import Noperthedron.Vertices.Python
import Noperthedron.Vertices.Trig
import Noperthedron.RationalApprox.RationalGlobal

/-!
# Global Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational global theorem. Everything
here is computable — no `noncomputable` keyword.
-/

namespace Noperthedron.Solution

abbrev Row.G_gt_maxH (r : Row) : Prop :=
  RationalApprox.GlobalTheorem.Gℚ r.interval.centerPose r.epsilon r.S r.w >
    RationalApprox.GlobalTheorem.maxHℚ r.interval.centerPose pythonPolyQ r.epsilon r.w

/-! ## The main checker -/

/-- Assertion that a row constitutes a valid application of the rational global theorem. -/
@[mk_iff]
structure Row.ValidGlobal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 1
  w_unit : row.wx_numerator ^ 2 + row.wy_numerator ^ 2 = (row.w_denominator : ℤ) ^ 2
  w_denominator_pos : 0 < row.w_denominator
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  epsilon_pos : 0 < row.epsilon
  G_gt_maxH : row.G_gt_maxH

instance (row : Row) : Decidable (Row.ValidGlobal row) :=
  decidable_of_iff _ (Row.validGlobal_iff row).symm

/-! ## Smoke test -/

/-- Row 91 from `data/solution_tree_300.csv` — the first global leaf. -/
def testGlobalRow : Row := {
  ID := 91, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := Interval.ofIntPose
    { θ₁ := 0, θ₂ := 806400, φ₁ := 0, φ₂ := 808960, α := -23459840 }
    { θ₁ := 806400, θ₂ := 1612800, φ₁ := 806400, φ₂ := 1617920, α := -22650880 }
    (by decide),
  S_index := VertexIndex.ofFin90 ⟨39, by omega⟩,
  wx_numerator := 5319166373, wy_numerator := 15662395164,
  w_denominator := 16540984045,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r' := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testGlobalRow.ValidGlobal

