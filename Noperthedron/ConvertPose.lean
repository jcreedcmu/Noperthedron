import Noperthedron.MatrixPose
import Noperthedron.Pose
import Noperthedron.Bounding.OrthEquivRotz

open scoped Matrix
open Real

/--
The matrix form of `rotRM θ φ α`, which is `Rz(-(π/2)) * Rz(α) * Ry(φ) * Rz(-θ)`.
-/
noncomputable
def rotRM_mat (θ φ α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Rz_mat (-(π / 2)) * Rz_mat α * Ry_mat φ * Rz_mat (-θ)

/--
The matrix `rotRM_mat θ φ α` is in SO3 because it's a product of SO3 matrices.
-/
lemma rotRM_mat_mem_SO3 (θ φ α : ℝ) :
    rotRM_mat θ φ α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  unfold rotRM_mat
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) ?_
  · exact Bounding.rot3_mat_mem_SO3 2 (-(π / 2))
  · exact Bounding.rot3_mat_mem_SO3 2 α
  · exact Bounding.rot3_mat_mem_SO3 1 φ
  · exact Bounding.rot3_mat_mem_SO3 2 (-θ)

/--
`rotRM θ φ α` equals the continuous linear map induced by `rotRM_mat θ φ α`.
-/
lemma rotRM_eq_rotRM_mat (θ φ α : ℝ) :
    rotRM θ φ α = (rotRM_mat θ φ α).toEuclideanLin.toContinuousLinearMap := by
  unfold rotRM rotRM_mat RzL RyL
  ext v i
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

noncomputable
def Pose.matrixPoseOfPose (p : Pose) : MatrixPose where
  innerRot := ⟨rotRM_mat p.θ₁ p.φ₁ p.α, rotRM_mat_mem_SO3 p.θ₁ p.φ₁ p.α⟩
  outerRot := ⟨rotRM_mat p.θ₂ p.φ₂ 0, rotRM_mat_mem_SO3 p.θ₂ p.φ₂ 0⟩
  innerOffset := 0

theorem converted_pose_inner_shadow_eq (v : Pose) (S : Set ℝ³) :
    innerShadow v S = innerShadow (v.matrixPoseOfPose) S := by
  -- Both sides are { proj_xyL (PoseLike.inner pose x) | x ∈ S }
  -- For Pose: PoseLike.inner v = (rotRM v.θ₁ v.φ₁ v.α).toAffineMap
  -- For MatrixPose with zero offset: PoseLike.inner = the inner rotation
  unfold innerShadow
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    congr 1
    simp only [PoseLike.inner, Pose.matrixPoseOfPose]
    simp only [AffineEquiv.coe_toAffineMap, AffineMap.coe_comp, Function.comp_apply,
      AffineEquiv.vaddConst_apply, LinearMap.coe_toAffineMap]
    rw [rotRM_eq_rotRM_mat]
    simp only [Matrix.toEuclideanLin_apply, inject_xy]
    ext i
    fin_cases i <;> simp [vadd_eq_add]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    congr 1
    simp only [PoseLike.inner, Pose.matrixPoseOfPose]
    simp only [AffineEquiv.coe_toAffineMap, AffineMap.coe_comp, Function.comp_apply,
      AffineEquiv.vaddConst_apply, LinearMap.coe_toAffineMap]
    rw [rotRM_eq_rotRM_mat]
    simp only [Matrix.toEuclideanLin_apply, inject_xy]
    ext i
    fin_cases i <;> simp [vadd_eq_add]

theorem converted_pose_outer_shadow_eq (v : Pose) (S : Set ℝ³) :
    outerShadow v S = outerShadow (v.matrixPoseOfPose) S := by
  unfold outerShadow
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    congr 1
    simp only [PoseLike.outer, Pose.matrixPoseOfPose]
    simp only [LinearMap.coe_toAffineMap]
    rw [rotRM_eq_rotRM_mat]
    rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    congr 1
    simp only [PoseLike.outer, Pose.matrixPoseOfPose]
    simp only [LinearMap.coe_toAffineMap]
    rw [rotRM_eq_rotRM_mat]
    rfl

theorem converted_pose_rupert_iff (v : Pose) (S : Set ℝ³) :
    RupertPose v S ↔ RupertPose (v.matrixPoseOfPose) S := by
  constructor; all_goals
  · unfold RupertPose
    rw [converted_pose_inner_shadow_eq, converted_pose_outer_shadow_eq]
    exact id

/--
Any SO3 matrix can be written in ZYZ Euler form: Rz(α) * Ry(β) * Rz(γ).
This is the classic Euler angle decomposition theorem.

Strategy: Given A ∈ SO3,
1. The third column of A is a unit vector v
2. By exists_SO3_mulVec_ez_eq, ∃ U = Rz(ϕ) * Ry(-θ) with U * e₃ = v
3. Then U⁻¹ * A fixes e₃, so by SO3_fixing_z_is_Rz it equals Rz(γ)
4. Therefore A = U * Rz(γ) = Rz(ϕ) * Ry(-θ) * Rz(γ)
-/
lemma SO3_euler_ZYZ (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ : ℝ, A = Rz_mat α * Ry_mat β * Rz_mat γ := by
  sorry -- TODO: Complete using exists_SO3_mulVec_ez_eq and SO3_fixing_z_is_Rz

/--
Given a MatrixPose with zero offset, there exists a 5-parameter Pose that produces
the same rotations. This follows from the ZYZ Euler angle decomposition.
-/
theorem pose_of_matrix_pose (p : MatrixPose) : ∃ pp : Pose, pp.matrixPoseOfPose = p.zeroOffset := by
  -- Decompose each SO3 matrix into Euler angles
  obtain ⟨α₁, β₁, γ₁, h_inner⟩ := SO3_euler_ZYZ p.innerRot.val p.innerRot.property
  obtain ⟨α₂, β₂, γ₂, h_outer⟩ := SO3_euler_ZYZ p.outerRot.val p.outerRot.property
  -- rotRM_mat θ φ α = Rz(-(π/2)) * Rz(α) * Ry(φ) * Rz(-θ) = Rz(α - π/2) * Ry(φ) * Rz(-θ)
  -- Match: Rz(α₁) * Ry(β₁) * Rz(γ₁) = Rz(α' - π/2) * Ry(φ') * Rz(-θ')
  -- Solution: α' = α₁ + π/2, φ' = β₁, θ' = -γ₁
  sorry -- TODO: Construct pose and prove equality using h_inner, h_outer
