module

public import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet
public import Noperthedron.CommonCenter
public import Noperthedron.Vertices.Exact
public import Noperthedron.MatrixPose

@[expose] public section

/-!
# Shadows, Rupert pairs and the separation criterion

`shadow R` is the projection of the Noperthedron under the matrix `R`. A Rupert pair
`(Ro, Ri)` has the closure of the inner shadow inside the interior of the outer one.
We reduce `IsRupert exactVerts` to the existence of a Rupert pair of rotations (using the
existing offset-removal argument), and prove the only non-Rupert criterion the checker
uses: an inner vertex that no outer vertex beats in some direction `w ≠ 0`.
-/

namespace Cayley

open Noperthedron
open scoped Matrix

/-- The shadow of the Noperthedron under `R`. -/
noncomputable def shadow (R : Matrix (Fin 3) (Fin 3) ℝ) : Set ℝ² :=
  (fun p => proj_xyL (R.toEuclideanLin p)) '' exactHull

/-- A Rupert passage with outer rotation `Ro` and inner rotation `Ri` (offset zero). -/
def RupPair (Ro Ri : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  closure (shadow Ri) ⊆ interior (shadow Ro)

/-- Copied from `NoperthedronIsNotRupert.lean` (it lives there next to the trig proof). -/
lemma rupert_set_implies_pose_rupert' {S : Set ℝ³} (r : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, inner_so3, offset, outer, outer_so3, sub⟩ := r
  let p : MatrixPose := MatrixPose.mk ⟨inner, inner_so3⟩ ⟨outer, outer_so3⟩ offset
  refine ⟨p, ?_⟩
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  simp only [innerShadow, outerShadow, Set.image, MatrixPose.inner_apply,
    MatrixPose.outer_apply, MatrixPose.projRot, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', ← proj_xy_eq_proj_xyL, add_comm]
  exact sub

theorem exists_rupPair (h : IsRupert exactVerts) :
    ∃ Ro ∈ SO3, ∃ Ri ∈ SO3, RupPair Ro Ri := by
  rw [rupert_iff_rupert_set exactVerts] at h
  have h' : IsRupertSet exactPolyhedron.hull := by
    simpa [exactVerts, exactPolyhedron, Polyhedron.hull, Set.range] using h
  obtain ⟨p, hp⟩ := rupert_set_implies_pose_rupert' h'
  have hconv : Convex ℝ exactPolyhedron.hull := by
    unfold Polyhedron.hull; exact convex_convexHull ℝ _
  have hz := rupert_implies_rot_rupert exactPolyhedron_point_symmetric hconv p hp
  refine ⟨p.outerRot.val, p.outerRot.property, p.innerRot.val, p.innerRot.property, ?_⟩
  have hhull : exactPolyhedron.hull = exactHull := exactPolyhedron_hull
  unfold RupPair shadow
  unfold RupertPose innerShadow outerShadow at hz
  rw [hhull, MatrixPose.zero_offset_elim] at hz
  convert hz using 3 <;> rfl

/-- The linear functional `x ↦ w₀ x₀ + w₁ x₁` on the first two coordinates. -/
def lin (w0 w1 : ℝ) (x : Fin 3 → ℝ) : ℝ := w0 * x 0 + w1 * x 1

theorem exactVertex_mem_hull (S : VertexIndex) : exactVertex S ∈ exactHull := by
  apply subset_convexHull
  simp [exactVerts]

theorem proj_xy_mat_mulVec_mul (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    ((proj_xy_mat * R) *ᵥ x) 0 = (R *ᵥ x) 0 ∧ ((proj_xy_mat * R) *ᵥ x) 1 = (R *ᵥ x) 1 := by
  rw [← Matrix.mulVec_mulVec]
  simp [proj_xy_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The separation criterion. -/
theorem not_rupPair_of_sep (Ro Ri : Matrix (Fin 3) (Fin 3) ℝ) (S : VertexIndex)
    (w0 w1 : ℝ) (hw : w0 ≠ 0 ∨ w1 ≠ 0)
    (h : ∀ T : VertexIndex,
      lin w0 w1 (Ro *ᵥ (exactVertex T).ofLp) ≤ lin w0 w1 (Ri *ᵥ (exactVertex S).ofLp)) :
    ¬ RupPair Ro Ri := by
  intro hR
  set c := lin w0 w1 (Ri *ᵥ (exactVertex S).ofLp)
  let q : ℝ² := proj_xyL (Ri.toEuclideanLin (exactVertex S))
  have hq : q ∈ shadow Ri := ⟨exactVertex S, exactVertex_mem_hull S, rfl⟩
  have hqi : q ∈ interior (shadow Ro) := hR (subset_closure hq)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hqi)
  let W : ℝ² := !₂[w0, w1]
  have hW : 0 < w0 ^ 2 + w1 ^ 2 := by
    rcases hw with h0 | h1
    · have := pow_pos (abs_pos.2 h0) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h1) 2; rw [sq_abs] at this; positivity
  set δ := ε / (2 * (‖W‖ + 1))
  have hδ : 0 < δ := by positivity
  have hmem : q + δ • W ∈ shadow Ro := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hδ.le]
    have h1 : ‖W‖ < ‖W‖ + 1 := by linarith
    have hne : ‖W‖ + 1 ≠ 0 := by positivity
    calc δ * ‖W‖ ≤ δ * (‖W‖ + 1) := by gcongr
      _ = ε / 2 := by simp only [δ]; field_simp
      _ < ε := by linarith
  obtain ⟨p, hp, hpq⟩ := hmem
  -- the functional is at most `c` on the hull
  have hlin : IsLinearMap ℝ (fun x : ℝ³ => lin w0 w1 (Ro *ᵥ x.ofLp)) := by
    constructor
    · intro x y
      simp only [lin, WithLp.ofLp_add, Matrix.mulVec_add, Pi.add_apply]; ring
    · intro a x
      simp only [lin, WithLp.ofLp_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]; ring
  have hhalf : exactHull ⊆ {x : ℝ³ | lin w0 w1 (Ro *ᵥ x.ofLp) ≤ c} := by
    apply convexHull_min
    · intro x hx
      simp only [exactVerts, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_range] at hx
      obtain ⟨T, rfl⟩ := hx
      exact h T
    · exact convex_halfSpace_le hlin c
  have hp' := hhalf hp
  simp only [Set.mem_ofPred_eq] at hp'
  have hval : lin w0 w1 (Ro *ᵥ p.ofLp) = c + δ * (w0 ^ 2 + w1 ^ 2) := by
    have h0 := congrArg (fun z : ℝ² => z 0) hpq
    have h1 := congrArg (fun z : ℝ² => z 1) hpq
    simp [proj_xyL, q, W, Matrix.toLpLin_apply] at h0 h1
    rw [(proj_xy_mat_mulVec_mul _ _).1, (proj_xy_mat_mulVec_mul _ _).1] at h0
    rw [(proj_xy_mat_mulVec_mul _ _).2, (proj_xy_mat_mulVec_mul _ _).2] at h1
    simp only [lin, c]
    rw [h0, h1]; ring
  nlinarith

end Cayley

end
