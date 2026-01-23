import Noperthedron.MatrixPose
import Noperthedron.Pose
import Noperthedron.Bounding.OrthEquivRotz

open Bounding Real
open scoped Matrix

/-- rotRM_mat is in SO3. -/
lemma rotRM_mat_mem_SO3 (θ φ α : ℝ) : rotRM_mat θ φ α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
    (rot3_mat_mem_SO3 2 _) (rot3_mat_mem_SO3 2 _)) (rot3_mat_mem_SO3 1 _)) (rot3_mat_mem_SO3 2 _)

/-- Convert a Pose to a MatrixPose. -/
noncomputable def Pose.matrixPoseOfPose (p : Pose) : MatrixPose where
  innerRot := ⟨rotRM_mat p.θ₁ p.φ₁ p.α, rotRM_mat_mem_SO3 _ _ _⟩
  outerRot := ⟨rotRM_mat p.θ₂ p.φ₂ 0, rotRM_mat_mem_SO3 _ _ _⟩
  innerOffset := 0

/-- inject_xy 0 = 0. -/
@[simp]
lemma inject_xy_zero : inject_xy (0 : ℝ²) = (0 : ℝ³) := by
  ext i
  fin_cases i <;> simp [inject_xy]

theorem converted_pose_inner_shadow_eq (v : Pose) (S : Set ℝ³) :
    innerShadow v S = innerShadow (v.matrixPoseOfPose) S := by
  simp only [innerShadow, PoseLike.inner]
  congr 1
  ext x
  constructor <;> (rintro ⟨v', hv', rfl⟩; exact ⟨v', hv', by simp [Pose.matrixPoseOfPose, rotRM_eq_rotRM_mat]⟩)

theorem converted_pose_outer_shadow_eq (v : Pose) (S : Set ℝ³) :
    outerShadow v S = outerShadow (v.matrixPoseOfPose) S := by
  simp only [outerShadow, PoseLike.outer]
  congr 1
  ext x
  simp [Pose.matrixPoseOfPose, rotRM_eq_rotRM_mat]

theorem converted_pose_rupert_iff (v : Pose) (S : Set ℝ³) :
    RupertPose v S ↔ RupertPose (v.matrixPoseOfPose) S := by
  constructor <;> (
    unfold RupertPose
    rw [converted_pose_inner_shadow_eq, converted_pose_outer_shadow_eq]
    exact id)

/-- Any SO3 matrix can be written as rotRM_mat θ φ α for some θ, φ, α.
Uses ZYZ Euler decomposition: M = Rz(a) * Ry(b) * Rz(c) = rotRM_mat (-c) b (a + π/2). -/
lemma SO3_to_rotRM_params (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ θ φ α, M = rotRM_mat θ φ α := by
  obtain ⟨a, b, c, h_decomp⟩ := SO3_ZYZ_decomposition M hM
  use -c, b, a + π / 2
  simp only [rotRM_mat, h_decomp, neg_neg, Rz_mat_mul_Rz_mat]
  ring_nf

/-- For a zeroOffset MatrixPose whose outer rotation is in rotRM form, we can construct
an equivalent Pose. -/
lemma pose_of_matrix_pose_with_outer_form (p : MatrixPose)
    (h_outer : ∃ θ₂ φ₂, p.outerRot.val = rotRM_mat θ₂ φ₂ 0) :
    ∃ pp : Pose, pp.matrixPoseOfPose = p.zeroOffset := by
  obtain ⟨θ₂, φ₂, h_out⟩ := h_outer
  obtain ⟨θ₁, φ₁, α, h_in⟩ := SO3_to_rotRM_params p.innerRot.val p.innerRot.property
  use { θ₁ := θ₁, θ₂ := θ₂, φ₁ := φ₁, φ₂ := φ₂, α := α }
  simp only [Pose.matrixPoseOfPose, MatrixPose.zeroOffset]
  congr 1 <;> apply Subtype.ext <;> simp [h_in.symm, h_out.symm]

/-- zeroOffset is idempotent when rotateBy preserves zero offset. -/
lemma zeroOffset_rotateBy_zeroOffset (p : MatrixPose) (δ : ℝ) :
    (p.zeroOffset.rotateBy δ).zeroOffset = p.zeroOffset.rotateBy δ := by
  simp [MatrixPose.zeroOffset, MatrixPose.rotateBy, map_zero]

/-- For any MatrixPose p, after rotating by the right δ, there exists a Pose
that equals the rotated zeroOffset. -/
theorem pose_of_matrix_pose (p : MatrixPose) :
    ∃ δ : ℝ, ∃ pp : Pose, pp.matrixPoseOfPose = (p.zeroOffset.rotateBy δ) := by
  obtain ⟨δ, θ, φ, h_form⟩ := exists_Rz_to_rotRM_form p.outerRot
  use δ
  have h_outer : ∃ θ₂ φ₂, (p.zeroOffset.rotateBy δ).outerRot.val = rotRM_mat θ₂ φ₂ 0 := by
    use θ, φ
    simp only [MatrixPose.rotateBy, MatrixPose.zeroOffset]
    exact h_form
  have h := pose_of_matrix_pose_with_outer_form (p.zeroOffset.rotateBy δ) h_outer
  rw [zeroOffset_rotateBy_zeroOffset] at h
  exact h
