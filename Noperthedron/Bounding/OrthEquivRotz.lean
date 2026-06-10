/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 120c93b3-4a3e-4d3e-830e-897e5a663c20

The following was proved by Aristotle:

- lemma rot3_rot3_orth_equiv_rotz {d d' : Fin 3} {α β : ℝ} :
    ∃ (u : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (γ : ℝ), γ ∈ Set.Ico (-π) π ∧
    rot3 d α ∘L rot3 d' β =
      u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap

-/

import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm
import Noperthedron.Bounding.BoundingUtil
import Noperthedron.RealMod

/-!

A crucial lemma for [SY25] Lemma 12.

-/

namespace Bounding

open Real
open scoped Real
open scoped Matrix

section AristotleLemmas

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

/-- Ry_mat transpose equals Ry_mat of negative angle. -/
lemma Ry_mat_transpose (θ : ℝ) : (Ry_mat θ).transpose = Ry_mat (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ry_mat, Matrix.transpose_apply, Real.cos_neg, Real.sin_neg]

/-- Rz(θ) * Rz(-θ) = 1. -/
lemma Rz_mat_mul_neg (θ : ℝ) : Rz_mat θ * Rz_mat (-θ) = 1 := by
  rw [← Rz_mat_transpose]
  exact (rot3_mat_mem_O3 2 θ).2

/-- Ry(θ) * Ry(-θ) = 1. -/
lemma Ry_mat_mul_neg (θ : ℝ) : Ry_mat θ * Ry_mat (-θ) = 1 := by
  rw [← Ry_mat_transpose]
  exact (rot3_mat_mem_O3 1 θ).2

/-- Rz(-θ) * Rz(θ) = 1. -/
lemma neg_Rz_mat_mul (θ : ℝ) : Rz_mat (-θ) * Rz_mat θ = 1 := by
  rw [← Rz_mat_transpose]
  exact (rot3_mat_mem_O3 2 θ).1

/-- Ry(-θ) * Ry(θ) = 1. -/
lemma neg_Ry_mat_mul (θ : ℝ) : Ry_mat (-θ) * Ry_mat θ = 1 := by
  rw [← Ry_mat_transpose]
  exact (rot3_mat_mem_O3 1 θ).1

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

/-- Rz(-α) applied to spherical vector removes azimuthal angle. -/
lemma Rz_neg_mulVec_spherical (α β : ℝ) :
    Rz_mat (-α) *ᵥ ![Real.sin β * Real.cos α, Real.sin β * Real.sin α, Real.cos β] =
    ![Real.sin β, 0, Real.cos β] := by
  ext i; fin_cases i <;> simp [Rz_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Real.cos_neg, Real.sin_neg]
  · have h := Real.cos_sq_add_sin_sq α; ring_nf; linear_combination Real.sin β * h
  · ring

/-- Ry(β) applied to xz-plane vector brings it to z-axis. -/
lemma Ry_mulVec_to_z (β : ℝ) :
    Ry_mat β *ᵥ ![Real.sin β, 0, Real.cos β] = ![(0:ℝ), 0, 1] := by
  ext i; fin_cases i <;> simp [Ry_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ring
  · linear_combination Real.sin_sq_add_cos_sq β

/--
ZYZ Euler decomposition: Any SO3 matrix can be written as Rz(α) * Ry(β) * Rz(γ).

Uses the fact that SO3 matrices preserve unit vectors and spherical coordinates.
-/
lemma SO3_ZYZ_decomposition (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ : ℝ, M = Rz_mat α * Ry_mat β * Rz_mat γ := by
  -- v = M * [0,0,1] is a unit vector
  let v : EuclideanSpace ℝ (Fin 3) := M.toEuclideanLin !₂[0, 0, 1]
  -- SO3 matrices preserve norms, so ‖v‖ = 1
  have hv_norm : ‖v‖ = 1 := by
    have h1 : v = OrthogonalGroup.toLinearIsometryEquiv ⟨M, hM.1⟩ !₂[0, 0, 1] := rfl
    rw [h1, LinearIsometryEquiv.norm_map]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  -- Use spherical coordinates: v = [sin β cos α, sin β sin α, cos β]
  obtain ⟨β, α, hv_eq⟩ := exists_spherical_coords v hv_norm
  -- N = Ry(β) * Rz(-α) * M fixes [0,0,1]
  -- (First Rz(-α) removes azimuthal angle, then Ry(β) brings to z-axis)
  let N := Ry_mat β * Rz_mat (-α) * M
  have hN_SO3 : N ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (rot3_mat_mem_SO3 1 β) (rot3_mat_mem_SO3 2 (-α))) hM
  have hN_fixes_z : N.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1] := by
    simp only [N, Matrix.mul_assoc, Matrix.toLpLin_apply]
    have hv_sph : M *ᵥ ![0, 0, 1] =
        ![Real.sin β * Real.cos α, Real.sin β * Real.sin α, Real.cos β] := by
      ext i
      simp only [v, Matrix.toLpLin_apply] at hv_eq
      exact congrFun hv_eq i
    have h_calc : (Ry_mat β * (Rz_mat (-α) * M)) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
      calc (Ry_mat β * (Rz_mat (-α) * M)) *ᵥ ![0, 0, 1]
          = Ry_mat β *ᵥ (Rz_mat (-α) *ᵥ (M *ᵥ ![0, 0, 1])) := by
              rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        _ = Ry_mat β *ᵥ ![Real.sin β, 0, Real.cos β] := by rw [hv_sph, Rz_neg_mulVec_spherical]
        _ = ![0, 0, 1] := Ry_mulVec_to_z β
    simp only [h_calc]
  -- By SO3_fixing_z_is_Rz, N = Rz(γ) for some γ
  obtain ⟨γ, hγ⟩ := SO3_fixing_z_is_Rz N hN_SO3 hN_fixes_z
  -- M = Rz(α) * Ry(-β) * Rz(γ) from N = Ry(β) * Rz(-α) * M = Rz(γ)
  use α, -β, γ
  have h2 : Ry_mat (-β) * Rz_mat γ = Rz_mat (-α) * M := by
    have h1 : Rz_mat γ = Ry_mat β * Rz_mat (-α) * M := hγ ▸ rfl
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, neg_Ry_mat_mul, Matrix.one_mul]
  calc M = Rz_mat α * (Rz_mat (-α) * M) := by
           rw [← Matrix.mul_assoc, Rz_mat_mul_neg, Matrix.one_mul]
       _ = Rz_mat α * (Ry_mat (-β) * Rz_mat γ) := by rw [h2]
       _ = Rz_mat α * Ry_mat (-β) * Rz_mat γ := by rw [Matrix.mul_assoc]

/-- Rz(0) = 1. -/
@[simp]
lemma Rz_mat_zero : Rz_mat 0 = 1 := by simp [Rz_mat, Matrix.one_fin_three]

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

lemma Rz_mod_two_pi (γ : ℝ) : ∃ γ' ∈ Set.Ioc (-π) π, Rz_mat γ = Rz_mat γ' := by
  use π - Real.emod (π - γ) (2 * π)
  refine ⟨?_, ?_⟩
  · have := Real.emod_in_interval (a := π - γ) (b := 2 * π) two_pi_pos
    grind
  · obtain ⟨k, hk⟩ := Real.emod_exists_multiple (π - γ) (2 * π) two_pi_pos
    simp [hk]

lemma SO3_is_conj_Rz_within_pi (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (_ : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (γ : ℝ),
      γ ∈ Set.Ioc (-π) π ∧ A = U * Rz_mat γ * U⁻¹ := by
  obtain ⟨U, U_SO, γ, hγ⟩ := SO3_is_conj_Rz A hA
  obtain ⟨γ', γ'_in, hγ'⟩ := Rz_mod_two_pi γ
  use U, U_SO, γ', γ'_in, hγ'▸hγ

end AristotleLemmas

lemma rot3_rot3_orth_equiv_rotz {d d' : Fin 3} {α β : ℝ} :
    ∃ (u : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (γ : ℝ), γ ∈ Set.Ioc (-π) π ∧
    rot3 d α ∘L rot3 d' β =
      u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap := by
  have dd'_so3 : rot3_mat d α * rot3_mat d' β ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (Bounding.rot3_mat_mem_SO3 d α) (Bounding.rot3_mat_mem_SO3 d' β)
  obtain ⟨U, hU, γ, hγ, h⟩ := SO3_is_conj_Rz_within_pi (rot3_mat d α * rot3_mat d' β) dd'_so3
  let u : Euc(3) ≃ₗᵢ[ℝ] Euc(3) := OrthogonalGroup.toLinearIsometryEquiv ⟨U, hU⟩
  have hu : ∀ x : Euc(3), u x = U.mulVec x :=
    OrthogonalGroup.toLinearIsometryEquiv_apply ⟨U, hU⟩
  have hU_det : IsUnit U.det := by
    have h1 := congrArg Matrix.det hU.2
    rw [Matrix.det_mul, Matrix.det_one] at h1
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h1)
  have hu_symm : ∀ x : Euc(3), u.symm x = WithLp.toLp 2 (U⁻¹.mulVec x) := by
    intro x
    apply u.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    refine WithLp.ofLp_injective 2 ?_
    rw [hu]
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU_det]
  refine ⟨u, γ, hγ, ?_⟩
  ext x i
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, hu,
    Matrix.mulVec]
  convert congr(Matrix.mulVec $h x i) using 1
  · have h_expand : ∀ (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : Euc(3)),
                      (A.toEuclideanLin (B.toEuclideanLin x)) = (A * B).mulVec x := by
      simp
    rw [←h_expand]
    fin_cases d <;> fin_cases d' <;> rfl
  · rw [show ∀ x : Euc(3), u.symm x = WithLp.toLp 2 (U⁻¹.mulVec x) from hu_symm]
    simp [RzL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp [Matrix.mul_apply]
    simp [Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Matrix.vecMul]
    ring_nf
