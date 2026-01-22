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
-- Any SO3 matrix that maps e₃ to v can be written as Rz(α) * Ry(β) for some α, β.
-- This follows from the spherical coordinate representation.
lemma SO3_maps_ez_to_v_is_ZY (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1)
    (hUv : U.mulVec ![0, 0, 1] = v.ofLp) :
    ∃ α β : ℝ, U = Rz_mat α * Ry_mat β := by
  sorry -- TODO: Derive from spherical coordinates

lemma SO3_euler_ZYZ (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ : ℝ, A = Rz_mat α * Ry_mat β * Rz_mat γ := by
  -- The third column of A is a unit vector
  let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 fun i => A i 2
  have hv_norm : ‖v‖ = 1 := by
    simp only [EuclideanSpace.norm_eq, v]
    have hATA := hA.1.1  -- A^T * A = 1
    have h22 := congrFun (congrFun hATA 2) 2
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_three,
      Matrix.star_apply, star_trivial] at h22
    rw [Real.sqrt_eq_one, Fin.sum_univ_three, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, sq_abs]
    convert h22 using 1
    ring
  -- Find U with U * e₃ = v (third column of A)
  obtain ⟨U, hU_SO3, hU_ez⟩ := Bounding.exists_SO3_mulVec_ez_eq v hv_norm
  -- U⁻¹ * A fixes e₃
  have hU_det : IsUnit U.det := by
    simp only [isUnit_iff_ne_zero, ne_eq]
    simp_all [Matrix.mem_specialOrthogonalGroup_iff]
  have hAe3 : A.mulVec ![0, 0, 1] = v.ofLp := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    fin_cases i <;> simp
  have hB_fixes_ez : (U⁻¹ * A).mulVec ![0, 0, 1] = ![0, 0, 1] := by
    rw [← Matrix.mulVec_mulVec, hAe3, ← hU_ez]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU_det, Matrix.one_mulVec]
  -- U⁻¹ * A ∈ SO3 and fixes e₃, so it's Rz(γ)
  have hB_SO3 : U⁻¹ * A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (Bounding.specialOrthogonalGroup_mem_inv hU_SO3) hA
  obtain ⟨γ, hγ⟩ := Bounding.SO3_fixing_z_is_Rz (U⁻¹ * A) hB_SO3 (by convert hB_fixes_ez; simp)
  -- A = U * Rz(γ)
  have hA_eq : A = U * Rz_mat γ := by
    calc A = U * (U⁻¹ * A) := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU_det, Matrix.one_mul]
      _ = U * Rz_mat γ := by rw [hγ]
  -- U = Rz(α) * Ry(β) by SO3_maps_ez_to_v_is_ZY
  obtain ⟨α, β, hU_eq⟩ := SO3_maps_ez_to_v_is_ZY U hU_SO3 v hv_norm hU_ez
  -- Therefore A = Rz(α) * Ry(β) * Rz(γ)
  exact ⟨α, β, γ, by rw [hA_eq, hU_eq]⟩

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
