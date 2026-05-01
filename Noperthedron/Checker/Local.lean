import Mathlib.Data.Finset.Max

import Noperthedron.Checker.ApproxSqrt
import Noperthedron.Local.Congruent
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.RationalLocal
import Noperthedron.SolutionTable.Defs
import Noperthedron.Vertices.Exact
import Noperthedron.Vertices.Python
import Noperthedron.Vertices.Symmetry
import Noperthedron.Vertices.Trig

/-!
# Local Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational local theorem. Everything
here is computable — no `noncomputable` keyword.
-/

namespace Noperthedron.Solution

abbrev sqrt_twoℚ : ℚ := 142 / 100

abbrev Row.Pi (r : Row) : Fin 3 → VertexIndex :=
  ![r.P1_index, r.P2_index, r.P3_index]

abbrev Row.Qi (r : Row) : Fin 3 → VertexIndex :=
  ![r.Q1_index, r.Q2_index, r.Q3_index]

noncomputable
abbrev Row.P (r : Row) : Local.Triangle :=
  ![exactVertex r.P1_index, exactVertex r.P2_index, exactVertex r.P3_index]

noncomputable
abbrev Row.Q (r : Row) : Local.Triangle :=
  ![exactVertex r.Q1_index, exactVertex r.Q2_index, exactVertex r.Q3_index]

abbrev Row.M₁_ (r : Row) : Matrix (Fin 2) (Fin 3) ℚ :=
  RationalApprox.rotMℚ_mat r.θ₁ r.φ₁

abbrev Row.M₂_ (r : Row) : Matrix (Fin 2) (Fin 3) ℚ :=
  RationalApprox.rotMℚ_mat r.θ₂ r.φ₂

abbrev Row.rotRℚ (r : Row) : Matrix (Fin 2) (Fin 2) ℚ :=
  RationalApprox.rotRℚ_mat r.α

abbrev Row.X₁ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₁ r.φ₁

abbrev Row.X₂ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₂ r.φ₂

abbrev rot90 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, -1; 1, 0]

abbrev Row.r (row : Row) : ℚ :=
  row.r' / 1000

open scoped Matrix
open RationalApprox (sqrtApprox)

abbrev Row.δ (row : Row) : ℚ :=
  Finset.max'
    (Finset.image
      (RationalApprox.LocalTheorem.BoundDeltaℚi row.interval.centerPose
         (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi) sqrtApprox) Finset.univ)
    (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)

/-- Assertion that a row constitutes a valid application of the rational global theorem. -/
@[mk_iff]
structure Row.ValidLocal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 2
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  exists_symmetry : ∃ s : TriangleSymmetry,
    s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)
  X₁_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₁ (pythonVertex ∘ row.Pi) row.epsilon 0 sqrtApprox
  X₂_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₂ (pythonVertex ∘ row.Qi) row.epsilon row.sigma_Q.val sqrtApprox
  P_spanning : ∀ i : Fin 3,
    2 * row.epsilon * (sqrt_twoℚ + row.epsilon) + 6 * κQ <
    (rot90 *ᵥ (row.M₁_ *ᵥ (pythonVertex (row.Pi i)))) ⬝ᵥ
      (row.M₁_ *ᵥ (pythonVertex ((row.Pi (i + 1)))))
  Q_spanning : ∀ i : Fin 3,
    2 * row.epsilon * (sqrt_twoℚ + row.epsilon) + 6 * κQ <
    (rot90 *ᵥ (row.M₂_ *ᵥ (pythonVertex (row.Qi i)))) ⬝ᵥ
      (row.M₂_ *ᵥ (pythonVertex ((row.Qi (i + 1)))))
  r_valid : RationalApprox.LocalTheorem.BoundRℚ
              row.r row.epsilon row.interval.centerPose (pythonVertex ∘ row.Qi) sqrtApprox
  Bεℚ : Local.TriangleQ.Bεℚ
    (pythonVertex ∘ row.Qi) row.Qi pythonVertex row.interval.centerPose
    row.epsilon row.δ row.r sqrtApprox

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
  interval := Interval.ofIntPose
    { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -22853120 }
    { θ₁ := 201600, θ₂ := 201600, φ₁ := 201600, φ₂ := 202240, α := -22650880 }
    (by decide),
  S_index := 0, wx_numerator := 0, wy_numerator := 0, w_denominator := 0,
  P1_index := VertexIndex.ofFin90 ⟨30, by lia⟩,
  P2_index := VertexIndex.ofFin90 ⟨31, by lia⟩,
  P3_index := VertexIndex.ofFin90 ⟨38, by lia⟩,
  Q1_index := VertexIndex.ofFin90 ⟨79, by lia⟩,
  Q2_index := VertexIndex.ofFin90 ⟨80, by lia⟩,
  Q3_index := VertexIndex.ofFin90 ⟨87, by lia⟩,
  r' := 0, sigma_Q := ⟨1, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testLocalRow.ValidLocal

/-
ID=2738018 from the full solution tree — a local leaf that requires
a reflection (k → -k) symmetry rather than just a rotation.
All vertices have i=1 (C2 orbit).

2738018,2,,,,0,403200,36691200,37094400,1209600,1612800,
11325440,11729920,-808960,-404480,
15,61,70,19,63,69,928,1,,,,
-/
def testLocalRowReflection : Row := {
  ID := 2738018, nodeType := 2, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := Interval.ofIntPose
    { θ₁ := 0, θ₂ := 1209600, φ₁ := 36691200, φ₂ := 11325440, α := -808960 }
    { θ₁ := 403200, θ₂ := 1612800, φ₁ := 37094400, φ₂ := 11729920, α := -404480 }
    (by decide),
  S_index := 0, wx_numerator := 0, wy_numerator := 0, w_denominator := 0,
  P1_index := VertexIndex.ofFin90 ⟨15, by lia⟩,
  P2_index := VertexIndex.ofFin90 ⟨61, by lia⟩,
  P3_index := VertexIndex.ofFin90 ⟨70, by lia⟩,
  Q1_index := VertexIndex.ofFin90 ⟨19, by lia⟩,
  Q2_index := VertexIndex.ofFin90 ⟨63, by lia⟩,
  Q3_index := VertexIndex.ofFin90 ⟨69, by lia⟩,
  r' := 928, sigma_Q := ⟨1, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testLocalRowReflection.ValidLocal
