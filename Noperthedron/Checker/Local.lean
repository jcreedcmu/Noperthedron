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

abbrev Row.X₁ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₁ r.φ₁

abbrev Row.X₂ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₂ r.φ₂

abbrev rot90 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, -1; 1, 0]

abbrev Row.r (row : Row) : ℚ :=
  row.r' / 1000

open scoped Matrix
open RationalApprox (sqrtApprox κℚ)

/-! ### `Row.δ`: max over per-`i` `BoundDeltaℚi` values, hoisting trig once -/

namespace Row.δ

open RationalApprox (sinℚ cosℚ)

/-- `BoundDeltaℚi` for a single `i`, with the 10 trig values used by
`M₁`, `R`, `M₂` (sin/cos of `θ₁ φ₁ α θ₂ φ₂`) passed in already evaluated. -/
@[inline] private def boundDelta_at (st1 ct1 sp1 cp1 sa ca st2 ct2 sp2 cp2 : ℚ)
    (P Q : Fin 3 → ℚ) : ℚ :=
  -- M₁ * P
  let m1p_0 := -st1 * P 0 + ct1 * P 1
  let m1p_1 := (-ct1 * cp1) * P 0 + (-st1 * cp1) * P 1 + sp1 * P 2
  -- R * (M₁ * P)
  let rm1p_0 := ca * m1p_0 + (-sa) * m1p_1
  let rm1p_1 := sa * m1p_0 + ca * m1p_1
  -- M₂ * Q
  let m2q_0 := -st2 * Q 0 + ct2 * Q 1
  let m2q_1 := (-ct2 * cp2) * Q 0 + (-st2 * cp2) * Q 1 + sp2 * Q 2
  let d0 := rm1p_0 - m2q_0
  let d1 := rm1p_1 - m2q_1
  let normSq := d0 * d0 + d1 * d1
  sqrtApprox.upper_sqrt.f normSq / 2 + 3 * κℚ

lemma boundDelta_at_eq (p : Pose ℚ) (P Q : Fin 3 → ℚ) :
    boundDelta_at (sinℚ p.θ₁) (cosℚ p.θ₁) (sinℚ p.φ₁) (cosℚ p.φ₁)
                  (sinℚ p.α) (cosℚ p.α)
                  (sinℚ p.θ₂) (cosℚ p.θ₂) (sinℚ p.φ₂) (cosℚ p.φ₂) P Q =
    sqrtApprox.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ P) - p.rotM₂ℚ Q) / 2 + 3 * κℚ := by
  unfold boundDelta_at RationalApprox.UpperSqrt.norm
  unfold Pose.rotRℚ Pose.rotM₁ℚ Pose.rotM₂ℚ
  unfold RationalApprox.rotRℚ RationalApprox.rotMℚ
  unfold RationalApprox.rotRℚ_mat RationalApprox.rotMℚ_mat
  rw [show (Matrix.toLin' _ : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ))
        ((Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) P) -
       (Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) Q
       = fun (j : Fin 2) =>
         (Matrix.toLin' _ ((Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) P)) j -
         ((Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) Q) j from rfl]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

end Row.δ

/-- The δ bound for a row: `max_i ‖R·M₁·P_i − M₂·Q_i‖ / 2 + 3κ`.
Equivalent to `Finset.max' (Finset.image BoundDeltaℚi univ) _` (see
`Row.δ_eq_max'_BoundDeltaℚi`), but the trig partial sums are hoisted once
per pose for a ~6× runtime speedup. -/
def Row.δ (row : Row) : ℚ :=
  let p := row.interval.centerPose
  let st1 := RationalApprox.sinℚ p.θ₁
  let ct1 := RationalApprox.cosℚ p.θ₁
  let sp1 := RationalApprox.sinℚ p.φ₁
  let cp1 := RationalApprox.cosℚ p.φ₁
  let sa  := RationalApprox.sinℚ p.α
  let ca  := RationalApprox.cosℚ p.α
  let st2 := RationalApprox.sinℚ p.θ₂
  let ct2 := RationalApprox.cosℚ p.θ₂
  let sp2 := RationalApprox.sinℚ p.φ₂
  let cp2 := RationalApprox.cosℚ p.φ₂
  let f : Fin 3 → ℚ := fun i =>
    Row.δ.boundDelta_at st1 ct1 sp1 cp1 sa ca st2 ct2 sp2 cp2
      (pythonVertex (row.Pi i)) (pythonVertex (row.Qi i))
  Finset.max' (Finset.image f Finset.univ)
    (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)

theorem Row.δ_eq_max'_BoundDeltaℚi (row : Row) :
    row.δ = Finset.max' (Finset.image
      (RationalApprox.LocalTheorem.BoundDeltaℚi row.interval.centerPose
        (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi) sqrtApprox) Finset.univ)
      (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩) := by
  show (Finset.image
        (fun i => Row.δ.boundDelta_at
          (RationalApprox.sinℚ row.interval.centerPose.θ₁)
          (RationalApprox.cosℚ row.interval.centerPose.θ₁)
          (RationalApprox.sinℚ row.interval.centerPose.φ₁)
          (RationalApprox.cosℚ row.interval.centerPose.φ₁)
          (RationalApprox.sinℚ row.interval.centerPose.α)
          (RationalApprox.cosℚ row.interval.centerPose.α)
          (RationalApprox.sinℚ row.interval.centerPose.θ₂)
          (RationalApprox.cosℚ row.interval.centerPose.θ₂)
          (RationalApprox.sinℚ row.interval.centerPose.φ₂)
          (RationalApprox.cosℚ row.interval.centerPose.φ₂)
          (pythonVertex (row.Pi i)) (pythonVertex (row.Qi i))) Finset.univ).max' _ =
      (Finset.image
        (RationalApprox.LocalTheorem.BoundDeltaℚi row.interval.centerPose
          (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi) sqrtApprox) Finset.univ).max' _
  congr 1
  apply Finset.image_congr
  intro i _
  unfold RationalApprox.LocalTheorem.BoundDeltaℚi
  exact Row.δ.boundDelta_at_eq _ _ _

/-- Assertion that a row constitutes a valid application of the rational global theorem. -/
@[mk_iff]
structure Row.ValidLocal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 2
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  epsilon_pos : 0 < row.epsilon
  exists_symmetry : ∃ s : TriangleSymmetry,
    s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)
  X₁_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₁ (pythonVertex ∘ row.Pi) row.epsilon 0 sqrtApprox
  X₂_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₂ (pythonVertex ∘ row.Qi) row.epsilon row.sigma_Q.val sqrtApprox
  P_spanning : ∀ i : Fin 3,
    2 * row.epsilon * (sqrt_twoℚ + row.epsilon) + 6 * κℚ <
    (rot90 *ᵥ (row.M₁_ *ᵥ (pythonVertex (row.Pi i)))) ⬝ᵥ
      (row.M₁_ *ᵥ (pythonVertex ((row.Pi (i + 1)))))
  Q_spanning : ∀ i : Fin 3,
    2 * row.epsilon * (sqrt_twoℚ + row.epsilon) + 6 * κℚ <
    (rot90 *ᵥ (row.M₂_ *ᵥ (pythonVertex (row.Qi i)))) ⬝ᵥ
      (row.M₂_ *ᵥ (pythonVertex ((row.Qi (i + 1)))))
  rpos : 0 < row.r
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
  ID := 245, nodeType := 2, nrChildren := 0, IDfirstChild := 0, split := 0,
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
  r' := 955, sigma_Q := ⟨1, by simp [Finset.mem_Icc]⟩
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
