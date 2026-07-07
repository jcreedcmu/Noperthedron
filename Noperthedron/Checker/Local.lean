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

abbrev Row.X₁ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₁ r.φ₁

abbrev Row.X₂ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₂ r.φ₂

abbrev rot90 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, -1; 1, 0]

abbrev Row.r (row : Row) : ℚ :=
  row.r' / 1000

open scoped Matrix
open RationalApprox (sqrtApprox κℚ)

/-! ### Spanning condition: hoisted trig, scalarized applied vectors -/

/-- The rational matrix form of the ε-κ-spanning condition on the triangle `T`
for angles `(θ, φ)` (cf. `Local.Triangle.κSpanning`). Named so that its
`Decidable` instance (via `Spanningℚ.check`) can hoist the trig entries of
`rotMℚ_mat θ φ` out of the `i`-loop and bind the applied vectors' components
as scalars; the generic `mulVec`/`dotProduct` instances would re-evaluate the
trig partial sums on every component access. -/
def Spanningℚ (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) : Prop :=
  ∀ i : Fin 3,
    2 * ε * (sqrt_twoℚ + ε) + 6 * κℚ <
    (rot90 *ᵥ (RationalApprox.rotMℚ_mat θ φ *ᵥ T i)) ⬝ᵥ
      (RationalApprox.rotMℚ_mat θ φ *ᵥ T (i + 1))

namespace Spanningℚ

open RationalApprox (sinℚ cosℚ)

/-- The spanning dot product `⟨rot90 · M·v, M·w⟩` in scalar form. -/
private lemma term_eq (θ φ : ℚ) (v w : Fin 3 → ℚ) :
    (rot90 *ᵥ (RationalApprox.rotMℚ_mat θ φ *ᵥ v)) ⬝ᵥ
      (RationalApprox.rotMℚ_mat θ φ *ᵥ w) =
    -(-cosℚ θ * cosℚ φ * v 0 + -sinℚ θ * cosℚ φ * v 1 + sinℚ φ * v 2) *
        (-sinℚ θ * w 0 + cosℚ θ * w 1) +
      (-sinℚ θ * v 0 + cosℚ θ * v 1) *
        (-cosℚ θ * cosℚ φ * w 0 + -sinℚ θ * cosℚ φ * w 1 + sinℚ φ * w 2) := by
  simp only [dotProduct, Matrix.mulVec, rot90, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, RationalApprox.rotMℚ_mat, neg_mul, Fin.sum_univ_three,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.sum_univ_two, zero_mul, add_zero, one_mul, neg_add_rev, neg_neg, zero_add]

/-- Bool-valued `Spanningℚ` check: trig partial sums are evaluated once per
pose and everything the `i`-loop touches is bound as a scalar. -/
def check (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) : Bool :=
  let st := sinℚ θ
  let ct := cosℚ θ
  let sp := sinℚ φ
  let cp := cosℚ φ
  let lhs := 2 * ε * (sqrt_twoℚ + ε) + 6 * κℚ
  (List.finRange 3).all fun i =>
    let v := T i
    let w := T (i + 1)
    let v0 := v 0
    let v1 := v 1
    let v2 := v 2
    let w0 := w 0
    let w1 := w 1
    let w2 := w 2
    decide (lhs <
      -(-ct * cp * v0 + -st * cp * v1 + sp * v2) * (-st * w0 + ct * w1) +
        (-st * v0 + ct * v1) * (-ct * cp * w0 + -st * cp * w1 + sp * w2))

theorem check_iff (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) :
    check θ φ ε T = true ↔ Spanningℚ θ φ ε T := by
  unfold check Spanningℚ
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  rw [term_eq θ φ (T i) (T (i + 1))]

instance instDecidable (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) :
    Decidable (Spanningℚ θ φ ε T) :=
  decidable_of_iff _ (check_iff θ φ ε T)

end Spanningℚ

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

/-! ### Precomputed pairwise vertex-difference norms for `Bεℚ`

The `n_dv` term of `Bεℚ.check` — `sqrtApprox.upper_sqrt.norm (Q_i − v_k)` —
is pose-independent, but costs a `sqrtℚUp` call on a denominator-`10³²`
input for each of the 270 `(i, k)` pairs of every local row. `sqrtDvTable`
precomputes all 90 × 90 pairs once per process, and `BεℚPy.check` is the
`pythonVertexA`/`sqrtApprox` specialization of `Bεℚ.check` that reads it
(the `Bεℚ` predicate itself is unchanged). -/

/-- Decode the flat index `45·ℓ + 15·i + k` (see `sqrtDv_eq`). -/
private def ofFlat (m : ℕ) (h : m < 90) : VertexIndex :=
  ⟨⟨m % 15, by omega⟩, ⟨m / 45, by omega⟩, ⟨m / 15 % 3, by omega⟩⟩

/-- All 90 × 90 pairwise `upper_sqrt` vertex-difference norms, indexed by the
flat pair index `flat a * 90 + flat b` with `flat ⟨k, ℓ, i⟩ = 45·ℓ + 15·i + k`. -/
def sqrtDvTable : Array ℚ :=
  Array.ofFn (n := 8100) fun j =>
    sqrtApprox.upper_sqrt.norm
      (pythonVertexA (ofFlat (j.val / 90) (by omega)) -
        pythonVertexA (ofFlat (j.val % 90) (by omega)))

/-- Table-backed pairwise vertex-difference norm: equal to
`sqrtApprox.upper_sqrt.norm (pythonVertexA a - pythonVertexA b)` by `sqrtDv_eq`. -/
def sqrtDv (a b : VertexIndex) : ℚ :=
  sqrtDvTable[(45 * a.ℓ.val + 15 * a.i.val + a.k.val) * 90 +
      (45 * b.ℓ.val + 15 * b.i.val + b.k.val)]'(by
    have h1 := a.ℓ.isLt
    have h2 := a.i.isLt
    have h3 := a.k.isLt
    have h4 := b.ℓ.isLt
    have h5 := b.i.isLt
    have h6 := b.k.isLt
    rw [sqrtDvTable, Array.size_ofFn]
    omega)

lemma sqrtDv_eq (a b : VertexIndex) :
    sqrtDv a b = sqrtApprox.upper_sqrt.norm (pythonVertexA a - pythonVertexA b) := by
  obtain ⟨ka, ℓa, ia⟩ := a
  obtain ⟨kb, ℓb, ib⟩ := b
  have h1 := ℓa.isLt
  have h2 := ia.isLt
  have h3 := ka.isLt
  have h4 := ℓb.isLt
  have h5 := ib.isLt
  have h6 := kb.isLt
  have e1 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) / 90 =
      45 * ℓa.val + 15 * ia.val + ka.val := by omega
  have e2 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) % 90 =
      45 * ℓb.val + 15 * ib.val + kb.val := by omega
  have f1 : (45 * ℓa.val + 15 * ia.val + ka.val) % 15 = ka.val := by omega
  have f2 : (45 * ℓa.val + 15 * ia.val + ka.val) / 45 = ℓa.val := by omega
  have f3 : (45 * ℓa.val + 15 * ia.val + ka.val) / 15 % 3 = ia.val := by omega
  have g1 : (45 * ℓb.val + 15 * ib.val + kb.val) % 15 = kb.val := by omega
  have g2 : (45 * ℓb.val + 15 * ib.val + kb.val) / 45 = ℓb.val := by omega
  have g3 : (45 * ℓb.val + 15 * ib.val + kb.val) / 15 % 3 = ib.val := by omega
  simp only [sqrtDv, sqrtDvTable, Array.getElem_ofFn, ofFlat, e1, e2, f1, f2, f3,
    g1, g2, g3, Fin.eta]

namespace BεℚPy

open Local.TriangleQ.Bεℚ (matEntries rotM₂Rℚ_c0 rotM₂Rℚ_c1)

/-- `Bεℚ.check` specialized to `pythonVertexA` and `sqrtApprox`: the
pose-independent `n_dv` norms come from `sqrtDvTable`, and the components of
`Q_i` are bound as scalars outside the `k`-loop. -/
def check (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε δ r : ℚ) : Bool :=
  let entries := matEntries p
  let bound := (δ + sqrtApprox.upper_sqrt_five * ε) / r
  (List.finRange 3).all fun i =>
    let Qi_idx := Qi i
    let Qi_val := pythonVertexA Qi_idx
    let qv0 := Qi_val 0
    let qv1 := Qi_val 1
    let qv2 := Qi_val 2
    let q0 := RationalApprox.round13 (entries.m₀₀ * qv0 + entries.m₀₁ * qv1 + entries.m₀₂ * qv2)
    let q1 := RationalApprox.round13 (entries.m₁₀ * qv0 + entries.m₁₁ * qv1 + entries.m₁₂ * qv2)
    let denom1 := sqrtApprox.upper_sqrt.f (q0 * q0 + q1 * q1)
                  + sqrtApprox.upper_sqrt_two * ε + 3 * κℚ
    decide <| ∀ k : VertexIndex, k ≠ Qi_idx →
      let vk := pythonVertexA k
      let dv0 := qv0 - vk 0
      let dv1 := qv1 - vk 1
      let dv2 := qv2 - vk 2
      let d0 := RationalApprox.round13 (entries.m₀₀ * dv0 + entries.m₀₁ * dv1 + entries.m₀₂ * dv2)
      let d1 := RationalApprox.round13 (entries.m₁₀ * dv0 + entries.m₁₁ * dv1 + entries.m₁₂ * dv2)
      let numer := q0 * d0 + q1 * d1 - 10 * κℚ
                   - 2 * ε * (sqrtDv Qi_idx k + 2 * κℚ) * (sqrtApprox.upper_sqrt_two + ε)
      let denom2 := sqrtApprox.upper_sqrt.f (d0 * d0 + d1 * d1)
                    + 2 * sqrtApprox.upper_sqrt_two * ε + 6 * κℚ
      bound < numer / (denom1 * denom2)

theorem check_iff (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε δ r : ℚ) :
    check Qi p ε δ r = true ↔
      Local.TriangleQ.Bεℚ Qi pythonVertexA p ε δ r sqrtApprox := by
  unfold check Local.TriangleQ.Bεℚ Local.TriangleQ.Bεℚ.lhs
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' (fun i => ?_)
  refine forall_congr' (fun k => ?_)
  refine forall_congr' (fun _ => ?_)
  simp only [show ∀ c : Fin 3, pythonVertexA (Qi i) c - pythonVertexA k c =
    (pythonVertexA (Qi i) - pythonVertexA k) c from fun _ => rfl]
  rw [sqrtDv_eq,
      ← rotM₂Rℚ_c0 p (pythonVertexA (Qi i)), ← rotM₂Rℚ_c1 p (pythonVertexA (Qi i)),
      ← rotM₂Rℚ_c0 p (pythonVertexA (Qi i) - pythonVertexA k),
      ← rotM₂Rℚ_c1 p (pythonVertexA (Qi i) - pythonVertexA k)]
  simp only [RationalApprox.UpperSqrt.norm, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]

/-- Specialized decision procedure for the `Bεℚ` conjunct of `Row.ValidLocal`;
the priority bump makes `Row.ValidLocal`'s `Decidable` instance pick it over
the generic `Bεℚ.instDecidable`. -/
instance (priority := high) instDecidablePy (Qi : Fin 3 → VertexIndex)
    (p : Pose ℚ) (ε δ r : ℚ) :
    Decidable (Local.TriangleQ.Bεℚ Qi pythonVertexA p ε δ r sqrtApprox) :=
  decidable_of_iff _ (check_iff Qi p ε δ r)

end BεℚPy

/-- Assertion that a row constitutes a valid application of the rational global theorem.

The vertex functions are the table-backed `pythonVertexA` (equal to
`pythonVertex` by `pythonVertexA_eq`), so the hot loops of the `Decidable`
instance read precomputed coordinates instead of re-dividing on every access. -/
@[mk_iff]
structure Row.ValidLocal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 2
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  epsilon_pos : 0 < row.epsilon
  exists_symmetry : ∃ s : TriangleSymmetry,
    s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)
  X₁_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₁ (pythonVertexA ∘ row.Pi) row.epsilon 0 sqrtApprox
  X₂_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₂ (pythonVertexA ∘ row.Qi) row.epsilon row.sigma_Q.val sqrtApprox
  P_spanning : Spanningℚ row.θ₁ row.φ₁ row.epsilon (pythonVertexA ∘ row.Pi)
  Q_spanning : Spanningℚ row.θ₂ row.φ₂ row.epsilon (pythonVertexA ∘ row.Qi)
  rpos : 0 < row.r
  r_valid : RationalApprox.LocalTheorem.BoundRℚ
              row.r row.epsilon row.interval.centerPose (pythonVertexA ∘ row.Qi) sqrtApprox
  Bεℚ : Local.TriangleQ.Bεℚ
    row.Qi pythonVertexA row.interval.centerPose
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
