import Noperthedron.MatrixPose
import Noperthedron.Pose
import Noperthedron.Bounding.OrthEquivRotz

open Bounding Real
open scoped Matrix

/-- Matrix version of rotRM. -/
noncomputable
def rotRM_mat (θ φ α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Rz_mat (-(π / 2)) * Rz_mat α * Ry_mat φ * Rz_mat (-θ)

/-- rotRM_mat is in SO3. -/
lemma rotRM_mat_mem_SO3 (θ φ α : ℝ) : rotRM_mat θ φ α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
    (rot3_mat_mem_SO3 2 _) (rot3_mat_mem_SO3 2 _)) (rot3_mat_mem_SO3 1 _)) (rot3_mat_mem_SO3 2 _)

/-- rotRM equals the EuclideanLin of rotRM_mat. -/
lemma rotRM_eq_rotRM_mat (θ φ α : ℝ) :
    rotRM θ φ α = (rotRM_mat θ φ α).toEuclideanLin.toContinuousLinearMap := by
  simp only [rotRM, rotRM_mat, RzL, RyL]
  ext v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc]

/-- rotRM_mat θ φ 0 simplifies to Rz(-π/2) * Ry(φ) * Rz(-θ). -/
lemma rotRM_mat_zero_alpha (θ φ : ℝ) : rotRM_mat θ φ 0 = Rz_mat (-(π / 2)) * Ry_mat φ * Rz_mat (-θ) := by
  simp only [rotRM_mat]
  rw [Rz_mat_zero, Matrix.mul_one]

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

/-- Convert a Pose to a MatrixPose. -/
noncomputable def Pose.matrixPoseOfPose (p : Pose) : MatrixPose where
  innerRot := ⟨rotRM_mat p.θ₁ p.φ₁ p.α, rotRM_mat_mem_SO3 _ _ _⟩
  outerRot := ⟨rotRM_mat p.θ₂ p.φ₂ 0, rotRM_mat_mem_SO3 _ _ _⟩
  innerOffset := 0

theorem converted_pose_inner_shadow_eq (v : Pose) (S : Set ℝ³) :
    innerShadow v S = innerShadow (v.matrixPoseOfPose) S := by
  -- Both sides are { proj_xyL (PoseLike.inner pose x) | x ∈ S }
  -- For Pose: PoseLike.inner v = (rotRM v.θ₁ v.φ₁ v.α).toAffineMap
  -- For MatrixPose with zero offset: PoseLike.inner = the inner rotation
  unfold innerShadow
  congr 1
  ext x
  constructor <;> (rintro ⟨y, hy, rfl⟩; refine ⟨y, hy, ?_⟩; congr 1)
  all_goals
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
  constructor <;> (rintro ⟨y, hy, rfl⟩; refine ⟨y, hy, ?_⟩; congr 1)
  all_goals
    simp only [PoseLike.outer, Pose.matrixPoseOfPose, LinearMap.coe_toAffineMap]
    rw [rotRM_eq_rotRM_mat]; rfl

theorem converted_pose_rupert_iff (v : Pose) (S : Set ℝ³) :
    RupertPose v S ↔ RupertPose (v.matrixPoseOfPose) S := by
  simp [RupertPose, converted_pose_inner_shadow_eq, converted_pose_outer_shadow_eq]

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
    · ext i; simp_all [Complex.ext_iff]; fin_cases i <;> tauto
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
    have h22 := congrFun (congrFun hA.1.1 2) 2
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_three,
      Matrix.star_apply, star_trivial] at h22
    simp only [Real.sqrt_eq_one, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    linarith
  -- Find α, β such that U := Rz(α) * Ry(β) maps e₃ to v (third column of A)
  obtain ⟨α, β, hU_SO3, hU_ez⟩ := exists_SO3_mulVec_ez_eq_ZY v hv_norm
  let U := Rz_mat α * Ry_mat β
  -- U⁻¹ * A fixes e₃
  have hU_det : IsUnit U.det := by
    simp only [isUnit_iff_ne_zero, ne_eq, U]
    simp_all [Matrix.mem_specialOrthogonalGroup_iff]
  have hB_fixes_ez : (U⁻¹ * A).mulVec ![0, 0, 1] = ![0, 0, 1] := by
    have hAe3 : A.mulVec ![0, 0, 1] = v.ofLp := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v]
    rw [← Matrix.mulVec_mulVec, hAe3, ← hU_ez,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU_det, Matrix.one_mulVec]
  obtain ⟨γ, hγ⟩ := Bounding.SO3_fixing_z_is_Rz (U⁻¹ * A)
    (Submonoid.mul_mem _ (Bounding.specialOrthogonalGroup_mem_inv hU_SO3) hA)
    (by convert hB_fixes_ez; simp)
  exact ⟨α, β, γ, by rw [← hγ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU_det, Matrix.one_mul]⟩

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
