import Noperthedron.MatrixPose
import Noperthedron.Pose
import Noperthedron.Bounding.OrthEquivRotz

open Bounding Real
open scoped Matrix

/-- Matrix version of rotRM. -/
noncomputable
def rotRM_mat (θ φ α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Rz_mat (-(π / 2)) * Rz_mat α * Ry_mat φ * Rz_mat (-θ)

/--
The matrix `rotRM_mat θ φ α` is in SO3 because it's a product of SO3 matrices.
-/
lemma rotRM_mat_mem_SO3 (θ φ α : ℝ) : rotRM_mat θ φ α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
    (Bounding.rot3_mat_mem_SO3 2 _) (Bounding.rot3_mat_mem_SO3 2 _))
    (Bounding.rot3_mat_mem_SO3 1 _)) (Bounding.rot3_mat_mem_SO3 2 _)

/--
`rotRM θ φ α` equals the continuous linear map induced by `rotRM_mat θ φ α`.
-/
lemma rotRM_eq_rotRM_mat (θ φ α : ℝ) :
    rotRM θ φ α = (rotRM_mat θ φ α).toEuclideanLin.toContinuousLinearMap := by
  ext v
  simp only [rotRM, rotRM_mat, RzL, RyL, ContinuousLinearMap.coe_comp', Function.comp_apply,
    LinearMap.coe_toContinuousLinearMap']
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- rotRM_mat θ φ 0 simplifies to Rz(-π/2) * Ry(φ) * Rz(-θ). -/
lemma rotRM_mat_zero_alpha (θ φ : ℝ) : rotRM_mat θ φ 0 = Rz_mat (-(π / 2)) * Ry_mat φ * Rz_mat (-θ) := by
  simp [rotRM_mat]

/-- For any SO3 matrix, there exists δ such that Rz(δ) * M has the form rotRM_mat θ φ 0. -/
lemma exists_Rz_to_rotRM_form (M : SO3) :
    ∃ δ θ φ, Rz_mat δ * M.val = rotRM_mat θ φ 0 := by
  obtain ⟨α, β, γ, h_decomp⟩ := SO3_ZYZ_decomposition M.val M.property
  use -(π / 2) - α, -γ, β
  rw [rotRM_mat_zero_alpha, h_decomp]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  congr 1
  · rw [Rz_mat_mul_Rz_mat]
    ring_nf
  · rw [neg_neg]

/-- inject_xy 0 = 0. -/
@[simp]
lemma inject_xy_zero : inject_xy (0 : ℝ²) = (0 : ℝ³) := by
  ext i; fin_cases i <;> simp [inject_xy]

/-- Convert a Pose to a MatrixPose. -/
noncomputable def Pose.matrixPoseOfPose (p : Pose) : MatrixPose where
  innerRot := ⟨rotRM_mat p.θ₁ p.φ₁ p.α, rotRM_mat_mem_SO3 _ _ _⟩
  outerRot := ⟨rotRM_mat p.θ₂ p.φ₂ 0, rotRM_mat_mem_SO3 _ _ _⟩
  innerOffset := 0

theorem converted_pose_inner_shadow_eq (v : Pose) (S : Set ℝ³) :
    innerShadow v S = innerShadow (v.matrixPoseOfPose) S := by
  simp [innerShadow, PoseLike.inner, Pose.matrixPoseOfPose, rotRM_eq_rotRM_mat]

theorem converted_pose_outer_shadow_eq (v : Pose) (S : Set ℝ³) :
    outerShadow v S = outerShadow (v.matrixPoseOfPose) S := by
  simp [outerShadow, PoseLike.outer, Pose.matrixPoseOfPose, rotRM_eq_rotRM_mat]

theorem converted_pose_rupert_iff (v : Pose) (S : Set ℝ³) :
    RupertPose v S ↔ RupertPose (v.matrixPoseOfPose) S := by
  simp [RupertPose, converted_pose_inner_shadow_eq, converted_pose_outer_shadow_eq]

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

/-- For any MatrixPose p, after rotating by the right δ, there exists a Pose
that equals the rotated zeroOffset. -/
theorem pose_of_matrix_pose (p : MatrixPose) :
    ∃ δ : ℝ, ∃ pp : Pose, pp.matrixPoseOfPose = (p.zeroOffset.rotateBy δ) := by
  obtain ⟨δ, θ, φ, h_form⟩ := exists_Rz_to_rotRM_form p.outerRot
  use δ
  have h_outer : ∃ θ₂ φ₂, (p.zeroOffset.rotateBy δ).outerRot.val = rotRM_mat θ₂ φ₂ 0 :=
    ⟨θ, φ, by simp only [MatrixPose.rotateBy, MatrixPose.zeroOffset]; exact h_form⟩
  simpa [MatrixPose.zeroOffset, MatrixPose.rotateBy] using
    pose_of_matrix_pose_with_outer_form (p.zeroOffset.rotateBy δ) h_outer
