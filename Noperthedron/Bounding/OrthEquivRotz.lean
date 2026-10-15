module

public import Noperthedron.Basic
public import Noperthedron.Bounding.OpNorm

public section

/-!
Rotations in `SO(3)`: one fixing `e_z` is some `Rz`, and every rotation is conjugate to some `Rz`.
-/

namespace Bounding

open Real
open scoped Real
open scoped Matrix

lemma rot3_mat_mem_SO3 (d : Fin 3) (θ : ℝ) :
    rot3_mat d θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨rot3_mat_mem_O3 d θ, ?_⟩
  fin_cases d <;> simp [rot3_mat, Rx_mat, Ry_mat, Rz_mat, Matrix.det_fin_three, ←sq]

lemma SO3_has_eigenvalue_one (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ A.toEuclideanLin v = v := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hA
  obtain ⟨A_in_O3, A_det_eq_one⟩ := hA
  rw [Matrix.mem_orthogonalGroup_iff] at A_in_O3
  have h_flip : (A - 1).det = -(A - 1).det :=
    calc (A - 1).det
    _ = ((A - 1) * Aᵀ).det := by simp [A_det_eq_one]
    _ = (1 - A)ᵀ.det := by simp [Matrix.sub_mul, A_in_O3]
    _ = (-(A - 1)).det := by rw [Matrix.det_transpose, neg_sub]
    _ = -(A - 1).det := by rw [Matrix.det_neg]; norm_num
  obtain ⟨v, v_nz, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (self_eq_neg.mp h_flip)
  exact ⟨WithLp.toLp 2 v, by simpa using v_nz, by simpa [sub_eq_zero, Matrix.sub_mulVec] using hv⟩

/-- Rz_mat transpose equals Rz_mat of negative angle. -/
lemma Rz_mat_transpose (θ : ℝ) : (Rz_mat θ).transpose = Rz_mat (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz_mat, Matrix.transpose_apply, Real.cos_neg, Real.sin_neg]

/-- Rz(θ) * Rz(-θ) = 1. -/
lemma Rz_mat_mul_neg (θ : ℝ) : Rz_mat θ * Rz_mat (-θ) = 1 := by
  rw [← Rz_mat_transpose]
  exact (rot3_mat_mem_O3 2 θ).2

/-- Rz(α) * Rz(β) = Rz(α + β). -/
lemma Rz_mat_mul_Rz_mat (α β : ℝ) : Rz_mat α * Rz_mat β = Rz_mat (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz_mat, cos_add, sin_add] <;> ring

lemma SO3_fixing_z_is_Rz (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hAz : A.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1]) :
    ∃ γ, A = Rz_mat γ := by
  rcases hA with ⟨hA₁, hA₂⟩
  simp_all [Matrix.mem_unitaryGroup_iff]
  -- Since $A$ is in $SO(3)$ and fixes the $z$-axis, its matrix representation must be of the form $\begin{pmatrix} \cos \gamma & -\sin \gamma & 0 \\ \sin \gamma & \cos \gamma & 0 \\ 0 & 0 & 1 \end{pmatrix}$ for some $\gamma$.
  -- Since A is in SO(3) and fixes the z-axis, the third row and column must be [0, 0, 1]. Therefore, A can be written as [[a, b, 0], [c, d, 0], [0, 0, 1]].
  obtain ⟨a, b, c, d, hA⟩ : ∃ a b c d : ℝ, A = !![a, b, 0; c, d, 0; 0, 0, 1] := by
    -- Since A fixes the z-axis, the third column of A must be [0, 0, 1].
    have h_third_col : A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 2 2 = 1 := by
      -- By definition of matrix multiplication, the third column of A is the image of the vector (0,0,1) under A.
      simp [ ← List.ofFn_inj, Matrix.mulVec ] at hAz
      aesop
    simp_all [← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.mul_apply, Fin.sum_univ_three,
              mul_self_add_mul_self_eq_zero ]
  -- Since A is in SO(3), we have a^2 + b^2 = 1 and c^2 + d^2 = 1, and ad - bc = 1.
  have h_conditions : a^2 + b^2 = 1 ∧ c^2 + d^2 = 1 ∧ a * d - b * c = 1 := by
    simp_all [← Matrix.ext_iff, Fin.forall_fin_succ]
    simp_all [Matrix.vecMul, Matrix.det_fin_three]
    exact ⟨by linarith, by linarith⟩
  -- Since $a^2 + b^2 = 1$ and $c^2 + d^2 = 1$, we can write $a = \cos \gamma$ and $b = -\sin \gamma$ for some $\gamma$.
  obtain ⟨γ, hγ, hγa, hγb⟩ : ∃ γ : ℝ, a = Real.cos γ ∧ b = -Real.sin γ := by
    refine ⟨Complex.arg (a + (-b) * Complex.I), ?_⟩
    rw [Complex.cos_arg, Complex.sin_arg] <;> simp [Complex.ext_iff]
    · simp [Complex.normSq, Complex.norm_def, ← sq, h_conditions]
    · aesop
  -- Since $c = \sin \gamma$ and $d = \cos \gamma$, we can substitute these into the matrix.
  have ⟨hc, hd⟩ : c = Real.sin γ ∧ d = Real.cos γ := by grind
  use γ
  simp_all

/-- Every unit vector in `ℝ³` has spherical coordinates. -/
lemma exists_spherical_coords (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    ∃ β α : ℝ, v = ![Real.sin β * Real.cos α, Real.sin β * Real.sin α, Real.cos β] := by
  simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, Fin.sum_univ_three, Fin.isValue,
    sqrt_eq_one, Nat.succ_eq_add_one, Nat.reduceAdd] at hv ⊢
  use Real.arccos (v 2), Complex.arg (v 0 + v 1 * Complex.I)
  have h_cos_sin : Real.cos (Real.arccos (v 2)) = v 2 ∧
      Real.sin (Real.arccos (v 2)) = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
    rw [Real.cos_arccos, Real.sin_arccos] <;>
      try linarith [sq_nonneg (1 + v 2), sq_nonneg (1 - v 2), sq_nonneg (v 0), sq_nonneg (v 1)]
    exact ⟨rfl, congrArg Real.sqrt <| sub_eq_iff_eq_add.mpr hv.symm⟩
  by_cases h : v 0 + v 1 * Complex.I = 0
  · simp_all
    simp_all [Complex.ext_iff]
    ext i
    fin_cases i <;> tauto
  · have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      rw [← Complex.normSq_add_mul_I]
      exact Complex.normSq_pos.mpr h
    simp_all [Complex.cos_arg, Complex.sin_arg]
    simp [Complex.normSq, Complex.norm_def] at *
    simp [← sq, mul_div_cancel₀ _ (ne_of_gt <| Real.sqrt_pos.mpr hpos)]
    ext i; fin_cases i <;> rfl

lemma exists_SO3_mulVec_ez_eq (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℝ, U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ U.mulVec ![0, 0, 1] = v := by
  obtain ⟨θ, ϕ, hθϕ⟩ := exists_spherical_coords v hv
  use rot3_mat 2 ϕ * rot3_mat 1 (-θ)
  constructor
  · exact Submonoid.mul_mem _ (rot3_mat_mem_SO3 2 ϕ) (rot3_mat_mem_SO3 1 _)
  · simp only [rot3_mat]
    ext i; fin_cases i <;> simp [hθϕ, Matrix.mulVec] <;> ring

lemma specialOrthogonalGroup_mem_inv {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (U_SO3 : U ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    U⁻¹ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  let u : Matrix.specialOrthogonalGroup (Fin n) ℝ := ⟨U, U_SO3⟩
  have h : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * U = 1 := by
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using
      congrArg Subtype.val (inv_mul_cancel u)
  rw [Matrix.inv_eq_left_inv h]
  exact u⁻¹.2

lemma SO3_is_conj_Rz (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (_ : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (γ : ℝ), A = U * Rz_mat γ * U⁻¹ := by
  obtain ⟨w, _⟩ := SO3_has_eigenvalue_one A hA
  let v := ‖w‖⁻¹ • w
  have A_fixes_v : A *ᵥ v = v := by
    have : (A.toEuclideanLin v).ofLp = v.ofLp := by simp_all [v]
    simpa [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  obtain ⟨U, U_SO3, U_z_eq_v⟩ := exists_SO3_mulVec_ez_eq v (by simp_all [v, norm_smul])
  let B := U⁻¹ * A * U
  have B_in_SO3 : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ hA) U_SO3
    exact specialOrthogonalGroup_mem_inv U_SO3
  have U_det_unit : IsUnit U.det := by
    simp only [isUnit_iff_ne_zero, ne_eq]
    simp_all [Matrix.mem_specialOrthogonalGroup_iff]
  have B_fixes_z :=
    calc B *ᵥ ![0, 0, 1]
    _ = U⁻¹ *ᵥ A *ᵥ (U *ᵥ ![0, 0, 1]) := by simp [B, Matrix.mul_assoc]
    _ = U⁻¹ *ᵥ (U *ᵥ ![0, 0, 1]) := by rw [U_z_eq_v, A_fixes_v]
    _ = (U⁻¹ * U) *ᵥ ![0, 0, 1] := by simp only [Matrix.mulVec_mulVec]
    _ = ![0, 0, 1] := by rw [Matrix.nonsing_inv_mul _ U_det_unit]; simp
  obtain ⟨γ, γb⟩ := SO3_fixing_z_is_Rz B B_in_SO3 (by convert B_fixes_z; simp)
  refine ⟨U, U_SO3.1, γ, ?_⟩
  simp only [← γb, B, ← mul_assoc, Matrix.mul_nonsing_inv U U_det_unit, one_mul]
  exact (U.mul_nonsing_inv_cancel_right A U_det_unit).symm

end Bounding

end
