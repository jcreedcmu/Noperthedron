module

public import Noperthedron.PentagonalHexecontahedron.HalfTurn

@[expose] public section

/-!
# Support-function witnesses (centrally symmetric solids)

For a centrally symmetric solid S the inner offset is irrelevant: if some
direction n of the projection plane and some vertex v_k of S have
⟪n, proj(innerRot v_k)⟫ ≥ max_{v ∈ S} ⟪n, proj(outerRot v)⟫, then no pose with
these rotations is Rupert (`not_rupertPose_of_witness`): the inner shadow's
points from ±v_k cannot both lie strictly inside the outer shadow's slab
|⟪n, ·⟫| < M. This is the certificate form of the DH's cap and tie checkers:
(R v_k)·d ≥ v_j·d for every vertex j, with d ⊥ the view.
-/

namespace Noperthedron.PentagonalHexecontahedron

open scoped RealInnerProductSpace

/-- A linear functional bounded by M on A is < M on the interior of A (n ≠ 0). -/
theorem inner_lt_of_mem_interior {A : Set ℝ²} {n : ℝ²} (hn : n ≠ 0) {M : ℝ}
    (hA : ∀ y ∈ A, ⟪n, y⟫ ≤ M) {y : ℝ²} (hy : y ∈ interior A) : ⟪n, y⟫ < M := by
  have hnhds : A ∈ nhds y := mem_interior_iff_mem_nhds.mp hy
  have hcont : Filter.Tendsto (fun t : ℝ => y + t • n) (nhds 0) (nhds y) := by
    have : Continuous (fun t : ℝ => y + t • n) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), y + t • n ∈ A :=
    (hcont.eventually hnhds).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have h := hA _ ht
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hpos : 0 < t * ‖n‖ ^ 2 := mul_pos ht0 (by positivity)
  linarith

theorem not_rupertPose_of_witness (p : MatrixPose) (S : Set ℝ³) (hS : ∀ v ∈ S, -v ∈ S)
    (n : ℝ²) (hn : n ≠ 0) (M : ℝ)
    (hM : ∀ v ∈ S, ⟪n, proj_xyL (PoseLike.outer p v)⟫ ≤ M)
    (vk : ℝ³) (hvk : vk ∈ S)
    (hw : M ≤ ⟪n, proj_xyL (p.innerRot.val.toEuclideanLin vk)⟫) :
    ¬ RupertPose p S := by
  intro h
  -- The outer shadow lies in the slab |⟪n, ·⟫| ≤ M.
  have hup : ∀ y ∈ outerShadow p S, ⟪n, y⟫ ≤ M := by
    rintro _ ⟨v, hv, rfl⟩
    exact hM v hv
  have hdown : ∀ y ∈ outerShadow p S, ⟪-n, y⟫ ≤ M := by
    rintro _ ⟨v, hv, rfl⟩
    have := hM (-v) (hS v hv)
    have hneg : proj_xyL (PoseLike.outer p (-v)) = -proj_xyL (PoseLike.outer p v) := by
      simp [PoseLike.outer, map_neg]
    rw [hneg, inner_neg_right] at this
    rw [inner_neg_left]
    exact this
  have hin : ∀ v ∈ S, proj_xyL (PoseLike.inner p v) ∈ interior (outerShadow p S) := by
    intro v hv
    exact h (subset_closure ⟨v, hv, rfl⟩)
  have h1 := inner_lt_of_mem_interior hn hup (hin vk hvk)
  have h2 := inner_lt_of_mem_interior (neg_ne_zero.mpr hn) hdown (hin (-vk) (hS vk hvk))
  rw [MatrixPose.inner_apply, map_add, proj_inject_xy, inner_add_right] at h1
  rw [MatrixPose.inner_apply, map_add, proj_inject_xy, inner_add_right, map_neg, map_neg,
    inner_neg_left, inner_neg_left, inner_neg_right, neg_neg] at h2
  linarith

end Noperthedron.PentagonalHexecontahedron
