module

public import Noperthedron.PentagonalHexecontahedron.IcoReduction

@[expose] public section

/-!
# The half-turn reduction (centrally symmetric solids)

For a centrally symmetric solid S (−S = S), turning the inner copy by the
half-turn H_z about the projection axis, composing it on the right with a
rotation G that preserves S, and negating the offset negates the inner
shadow; the outer shadow is symmetric, so the pose stays Rupert iff it was
(`RupertPose_leftHalfTurn_iff`). With the outer view u = outerRotᵀ e_z the
relative rotation becomes H_u R G (`relativeRotation_leftHalfTurn`), so the
relative rotation may be reduced modulo R ↦ H_u R g, g ∈ I: the deltoidal
hexecontahedron's mirror coincidences σ_u σ = H_u H_n are equivalent to the
identity (notes/T.md).
-/

namespace Noperthedron.PentagonalHexecontahedron

open scoped Matrix

/-- The half-turn about the projection axis z. -/
def halfTurnZMat : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

theorem halfTurnZMat_mem : halfTurnZMat ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [halfTurnZMat, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [halfTurnZMat, Matrix.det_fin_three]

noncomputable def halfTurnZ : SO3 := ⟨halfTurnZMat, halfTurnZMat_mem⟩

theorem proj_halfTurnZ (v : ℝ³) :
    proj_xyL (halfTurnZMat.toEuclideanLin v) = -proj_xyL v := by
  ext i
  fin_cases i <;>
    simp [proj_xyL, proj_xy_mat, halfTurnZMat, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

/-- Turn the inner copy by H_z, compose it with G on the right, negate the offset. -/
noncomputable def _root_.MatrixPose.leftHalfTurn (p : MatrixPose) (G : SO3) : MatrixPose where
  innerRot := halfTurnZ * p.innerRot * G
  outerRot := p.outerRot
  innerOffset := -p.innerOffset

theorem proj_inject_xy (w : ℝ²) : proj_xyL (inject_xy w) = w := by
  ext i
  fin_cases i <;> simp [proj_xyL, proj_xy_mat, inject_xy, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]

theorem proj_inner_leftHalfTurn (p : MatrixPose) (G : SO3) (v : ℝ³) :
    proj_xyL (PoseLike.inner (p.leftHalfTurn G) v) =
      -proj_xyL (PoseLike.inner p (G.val.toEuclideanLin v)) := by
  rw [MatrixPose.inner_apply, MatrixPose.inner_apply, map_add, map_add, proj_inject_xy,
    proj_inject_xy]
  have h : (p.leftHalfTurn G).innerRot.val.toEuclideanLin v =
      halfTurnZMat.toEuclideanLin (p.innerRot.val.toEuclideanLin (G.val.toEuclideanLin v)) := by
    simp [MatrixPose.leftHalfTurn, halfTurnZ, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [h, proj_halfTurnZ]
  simp [MatrixPose.leftHalfTurn]
  abel

theorem innerShadow_leftHalfTurn (p : MatrixPose) (G : SO3) (S : Set ℝ³)
    (hG : G.val.toEuclideanLin '' S = S) :
    innerShadow (p.leftHalfTurn G) S = -innerShadow p S := by
  ext w
  simp only [innerShadow, Set.mem_setOf_eq, Set.mem_neg]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨G.val.toEuclideanLin v, ?_, ?_⟩
    · rw [← hG]
      exact ⟨v, hv, rfl⟩
    · rw [proj_inner_leftHalfTurn, neg_neg]
  · rintro ⟨v, hv, hw⟩
    have hv' : v ∈ G.val.toEuclideanLin '' S := by rwa [hG]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    rw [proj_inner_leftHalfTurn, hw, neg_neg]

theorem outerShadow_leftHalfTurn (p : MatrixPose) (G : SO3) (S : Set ℝ³) :
    outerShadow (p.leftHalfTurn G) S = outerShadow p S := rfl

theorem neg_outerShadow (p : MatrixPose) (S : Set ℝ³) (hS : ∀ v ∈ S, -v ∈ S) :
    -outerShadow p S = outerShadow p S := by
  have hproj : ∀ v : ℝ³, proj_xyL (PoseLike.outer p (-v)) = -proj_xyL (PoseLike.outer p v) := by
    intro v
    simp [PoseLike.outer, map_neg]
  ext w
  simp only [outerShadow, Set.mem_setOf_eq, Set.mem_neg]
  constructor
  · rintro ⟨v, hv, hw⟩
    exact ⟨-v, hS v hv, by rw [hproj, hw, neg_neg]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨-v, hS v hv, by rw [hproj]⟩

/-- The half-turn reduction preserves Rupert poses of a centrally symmetric
solid. -/
theorem RupertPose_leftHalfTurn_iff (p : MatrixPose) (G : SO3) (S : Set ℝ³)
    (hG : G.val.toEuclideanLin '' S = S) (hS : ∀ v ∈ S, -v ∈ S) :
    RupertPose (p.leftHalfTurn G) S ↔ RupertPose p S := by
  have himg : ∀ B : Set ℝ², (fun a : ℝ² => -a) '' B = -B := fun B => by
    ext x
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-x, hx, neg_neg x⟩
  have hclosure : ∀ A : Set ℝ², closure (-A) = -closure A := by
    intro A
    have h := (Homeomorph.neg ℝ²).image_closure A
    simp only [Homeomorph.coe_neg] at h
    rw [himg, himg] at h
    exact h.symm
  have hinterior : ∀ A : Set ℝ², interior (-A) = -interior A := by
    intro A
    have h := (Homeomorph.neg ℝ²).image_interior A
    simp only [Homeomorph.coe_neg] at h
    rw [himg, himg] at h
    exact h.symm
  unfold RupertPose
  rw [innerShadow_leftHalfTurn p G S hG, outerShadow_leftHalfTurn, hclosure]
  constructor
  · intro h
    have h' := Set.neg_subset_neg.mpr h
    rwa [neg_neg, ← hinterior, neg_outerShadow p S hS] at h'
  · intro h
    have h' := Set.neg_subset_neg.mpr h
    rwa [← hinterior, neg_outerShadow p S hS] at h'

end Noperthedron.PentagonalHexecontahedron
