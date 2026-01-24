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
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Rz matrices multiply by adding angles. -/
lemma Rz_mat_mul (a b : ℝ) : Rz_mat a * Rz_mat b = Rz_mat (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rz_mat, cos_add, sin_add] <;> ring

/-- Collapse leading Rz terms: `rotRM_mat θ φ α = Rz(α - π/2) * Ry(φ) * Rz(-θ)`. -/
lemma rotRM_mat_eq (θ φ α : ℝ) :
    rotRM_mat θ φ α = Rz_mat (α - π / 2) * Ry_mat φ * Rz_mat (-θ) := by
  simp only [rotRM_mat, Rz_mat_mul, sub_eq_add_neg, add_comm]

/-- inject_xy 0 = 0. -/
@[simp]
lemma inject_xy_zero : inject_xy (0 : ℝ²) = (0 : ℝ³) := by
  ext i; fin_cases i <;> simp [inject_xy]

noncomputable
def Pose.matrixPoseOfPose (p : Pose) : MatrixPose where
  innerRot := ⟨rotRM_mat p.θ₁ p.φ₁ p.α, rotRM_mat_mem_SO3 p.θ₁ p.φ₁ p.α⟩
  outerRot := ⟨rotRM_mat p.θ₂ p.φ₂ 0, rotRM_mat_mem_SO3 p.θ₂ p.φ₂ 0⟩
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

/--
Given a MatrixPose with zero offset whose outer rotation is in the image of `rotRM_mat _ _ 0`,
there exists a 5-parameter Pose that produces the same MatrixPose.

Note: The assumption `h_outer` is necessary because `rotRM_mat θ φ 0 = Rz(-π/2) * Ry(φ) * Rz(-θ)`
has only 2 DOF (the first Euler angle is fixed at -π/2), while a general SO3 matrix has 3 DOF.
-/
theorem pose_of_matrix_pose (p : MatrixPose)
    (h_outer : ∃ θ φ, p.outerRot.val = rotRM_mat θ φ 0) :
    ∃ pp : Pose, pp.matrixPoseOfPose = p.zeroOffset := by
  obtain ⟨α₁, β₁, γ₁, h_inner⟩ := SO3_euler_ZYZ p.innerRot.val p.innerRot.property
  obtain ⟨θ₂, φ₂, h_outer⟩ := h_outer
  let pp : Pose := { θ₁ := -γ₁, φ₁ := β₁, α := α₁ + π / 2, θ₂ := θ₂, φ₂ := φ₂ }
  refine ⟨pp, ?_⟩
  simp only [Pose.matrixPoseOfPose, MatrixPose.zeroOffset, pp]
  congr 1
  · -- innerRot: use rotRM_mat_eq to simplify
    apply Subtype.ext
    calc rotRM_mat (-γ₁) β₁ (α₁ + π / 2)
        = Rz_mat α₁ * Ry_mat β₁ * Rz_mat γ₁ := by
          simp only [rotRM_mat_eq, neg_neg]
          ring_nf
      _ = p.innerRot.val := h_inner.symm
  · -- outerRot: direct from h_outer
    apply Subtype.ext
    exact h_outer.symm
