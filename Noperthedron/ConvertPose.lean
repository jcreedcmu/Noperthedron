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

/-- For any unit vector v, there exist angles α, β such that Rz(α) * Ry(β) is in SO3
and maps e₃ to v. Uses spherical coordinates: θ = arccos(v₂), ϕ = arg(v₀ + v₁·i).
This is the same construction as exists_SO3_mulVec_ez_eq but exposing the angles. -/
lemma exists_SO3_mulVec_ez_eq_ZY (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    ∃ α β : ℝ, let U := Rz_mat α * Ry_mat β
      U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ U.mulVec ![0, 0, 1] = v := by
  -- Copy of exists_SO3_mulVec_ez_eq proof, adapted to return (α, β)
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_three] at hv
  obtain ⟨θ, ϕ, hθϕ⟩ : ∃ θ ϕ : ℝ, v = ![sin θ * cos ϕ, sin θ * sin ϕ, cos θ] := by
    use Real.arccos (v 2), Complex.arg (v 0 + v 1 * Complex.I)
    have h_cos_sin : cos (Real.arccos (v 2)) = v 2 ∧ sin (Real.arccos (v 2)) = √(v 0 ^ 2 + v 1 ^ 2) := by
      rw [Real.cos_arccos, Real.sin_arccos] <;> try nlinarith
      exact ⟨rfl, congrArg Real.sqrt <| sub_eq_iff_eq_add.mpr hv.symm⟩
    by_cases h : v 0 + v 1 * Complex.I = 0 <;> simp_all [Complex.cos_arg, Complex.sin_arg]
    · simp_all [Complex.ext_iff]
      ext i; fin_cases i <;> tauto
    · simp [Complex.normSq, Complex.norm_def] at *
      simp [← sq, mul_div_cancel₀ _ (show √(v 0 ^ 2 + v 1 ^ 2) ≠ 0 from ne_of_gt <| Real.sqrt_pos.mpr <|
        by nlinarith [mul_self_pos.mpr <| show v 0 ^ 2 + v 1 ^ 2 ≠ 0 from
          fun h' => h <| by norm_num [Complex.ext_iff, sq]; constructor <;> nlinarith])]
      ext i; fin_cases i <;> rfl
  use ϕ, -θ
  constructor
  · exact Submonoid.mul_mem _ (Bounding.rot3_mat_mem_SO3 2 ϕ) (Bounding.rot3_mat_mem_SO3 1 (-θ))
  · simp only [Rz_mat, Ry_mat]
    ext i; fin_cases i <;> simp [hθϕ, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- Any SO3 matrix can be written in ZYZ Euler form: Rz(α) * Ry(β) * Rz(γ).
Strategy: extract third column v, find Rz(α) * Ry(β) mapping e₃ to v, then the
remainder fixes e₃ so must be Rz(γ). -/
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
  -- Find α, β such that U := Rz(α) * Ry(β) maps e₃ to v (third column of A)
  obtain ⟨α, β, hU_SO3, hU_ez⟩ := exists_SO3_mulVec_ez_eq_ZY v hv_norm
  let U := Rz_mat α * Ry_mat β
  -- U⁻¹ * A fixes e₃
  have hU_det : IsUnit U.det := by
    simp only [isUnit_iff_ne_zero, ne_eq, U]
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
  -- A = U * Rz(γ) = Rz(α) * Ry(β) * Rz(γ)
  have hA_eq : A = U * Rz_mat γ := by
    calc A = U * (U⁻¹ * A) := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU_det, Matrix.one_mul]
      _ = U * Rz_mat γ := by rw [hγ]
  exact ⟨α, β, γ, hA_eq⟩

/--
**FALSE AS STATED**: This theorem claims that every MatrixPose with zero offset can be
converted to a 5-parameter Pose. However, this is impossible due to degree-of-freedom mismatch:

- **Inner rotation**: `rotRM_mat θ φ α` has 3 DOF (θ, φ, α), which can match any SO3 matrix
  via ZYZ Euler angles: set α = α₁ + π/2, φ = β₁, θ = -γ₁ for A = Rz(α₁) * Ry(β₁) * Rz(γ₁).

- **Outer rotation**: `rotRM_mat θ φ 0 = Rz(-π/2) * Ry(φ) * Rz(-θ)` has only 2 DOF (θ, φ).
  The first Euler angle is fixed at -π/2. A general SO3 matrix A = Rz(α) * Ry(β) * Rz(γ)
  can only be matched if α ≡ -π/2 (mod 2π), which is not always the case.

**Consequence**: A 5-parameter Pose (with rotations θ₁, φ₁, θ₂, φ₂, α) has effectively
5 DOF for rotations, but a MatrixPose has 6 DOF (3 for inner + 3 for outer).

**To make this provable**, add the assumption:
  `∃ θ φ, p.outerRot.val = rotRM_mat θ φ 0`

This would require updating `no_nopert_rot_pose` in Final.lean, which currently depends on
this theorem to convert arbitrary zero-offset MatrixPoses to Poses.
-/
theorem pose_of_matrix_pose (p : MatrixPose) : ∃ pp : Pose, pp.matrixPoseOfPose = p.zeroOffset := by
  -- Inner rotation: solvable via ZYZ Euler angles
  obtain ⟨α₁, β₁, γ₁, h_inner⟩ := SO3_euler_ZYZ p.innerRot.val p.innerRot.property
  -- Outer rotation: ZYZ decomposition
  obtain ⟨α₂, β₂, γ₂, h_outer⟩ := SO3_euler_ZYZ p.outerRot.val p.outerRot.property
  -- Construct the Pose:
  -- For inner: rotRM_mat θ φ α = Rz(-π/2) * Rz(α) * Ry(φ) * Rz(-θ)
  --   Matching Rz(α₁) * Ry(β₁) * Rz(γ₁): set α = α₁ + π/2, φ = β₁, θ = -γ₁
  -- For outer: rotRM_mat θ φ 0 = Rz(-π/2) * Ry(φ) * Rz(-θ)
  --   This requires the first Euler angle to be -π/2, which is NOT always true!
  let pp : Pose := {
    θ₁ := -γ₁
    φ₁ := β₁
    α := α₁ + π / 2
    θ₂ := -γ₂
    φ₂ := β₂
  }
  use pp
  simp only [Pose.matrixPoseOfPose, MatrixPose.zeroOffset]
  congr 1
  · -- innerRot: provable
    apply Subtype.ext
    simp only [rotRM_mat]
    -- Need: Rz(-π/2) * Rz(α₁ + π/2) * Ry(β₁) * Rz(γ₁) = Rz(α₁) * Ry(β₁) * Rz(γ₁)
    rw [h_inner]
    -- Unfold pp's fields: pp.θ₁ = -γ₁, pp.φ₁ = β₁, pp.α = α₁ + π/2
    simp only [pp]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rz_mat, Ry_mat, Matrix.mul_apply,
      Fin.sum_univ_three, neg_neg, cos_neg, sin_neg, cos_add_pi_div_two, sin_add_pi_div_two]
  · -- outerRot: STUCK - requires α₂ = -π/2 but α₂ can be any angle
    apply Subtype.ext
    simp only [rotRM_mat, pp]
    rw [h_outer]
    -- Goal: Rz(-π/2) * Rz(0) * Ry(β₂) * Rz(γ₂) = Rz(α₂) * Ry(β₂) * Rz(γ₂)
    -- Since Rz(0) = I, this simplifies to:
    --   Rz(-π/2) * Ry(β₂) * Rz(γ₂) = Rz(α₂) * Ry(β₂) * Rz(γ₂)
    -- Since Ry(β₂) * Rz(γ₂) is invertible (as an SO3 matrix), this requires:
    --   Rz(-π/2) = Rz(α₂), i.e., α₂ = -π/2 (mod 2π)
    -- But α₂ is an ARBITRARY Euler angle determined by p.outerRot, so this is FALSE in general.
    -- COUNTEREXAMPLE: Any MatrixPose whose outer rotation has first ZYZ Euler angle ≠ -π/2.
    sorry
