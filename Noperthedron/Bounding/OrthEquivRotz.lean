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
import Noperthedron.Bounding.RaRa
import Noperthedron.Bounding.Lemma11
import Noperthedron.Bounding.BoundingUtil
import Noperthedron.RealMod

/-!

A crucial lemma for [SY25] Lemma 12.

-/

namespace Bounding

open Real
open scoped Real

section AristotleLemmas

open scoped Matrix
open Bounding

lemma rot3_mat_mem_O3 (d : Fin 3) (θ : ℝ) :
    rot3_mat d θ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  unfold rot3_mat
  fin_cases d <;>
  · constructor <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
      · try simp [Matrix.mul_apply, Fin.sum_univ_succ]
        try ring_nf
        try simp [Real.sin_sq]

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

lemma exists_SO3_mulVec_ez_eq (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℝ, U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ U.mulVec ![0, 0, 1] = v := by
  -- Let $U$ be a rotation matrix such that $U \cdot \mathbf{e}_3 = v$. Since $v$ is a unit vector, we can construct such a matrix using the Rodrigues' rotation formula. We'll use the fact that any unit vector in $\mathbb{R}^3$ can be written as $v = \cos \theta \mathbf{e}_3 + \sin \theta (\cos \phi \mathbf{e}_1 + \sin \phi \mathbf{e}_2)$ for some $\theta$ and $\phi$.
  obtain ⟨θ, ϕ, hθϕ⟩ : ∃ θ ϕ : ℝ, v = ![Real.sin θ * Real.cos ϕ, Real.sin θ * Real.sin ϕ, Real.cos θ] := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_three] at hv ⊢
    use Real.arccos ( v 2 ), Complex.arg (v 0 + v 1 * Complex.I)
    -- By definition of arccos and argument, we can express v 0, v 1, and v 2 in terms of θ and ϕ.
    have h_cos_sin : Real.cos (Real.arccos (v 2)) = v 2 ∧ Real.sin (Real.arccos (v 2)) = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
      rw [ Real.cos_arccos, Real.sin_arccos ] <;> try nlinarith
      exact ⟨rfl, congrArg Real.sqrt <| sub_eq_iff_eq_add.mpr hv.symm⟩
    by_cases h : v 0 + v 1 * Complex.I = 0 <;> simp_all [Complex.cos_arg, Complex.sin_arg]
    · simp_all [Complex.ext_iff]
      ext i
      fin_cases i <;> tauto
    · simp [Complex.normSq, Complex.norm_def] at *
      simp [← sq, mul_div_cancel₀ _ (show √( v 0 ^ 2 + v 1 ^ 2 ) ≠ 0 from ne_of_gt <| Real.sqrt_pos.mpr <| by nlinarith [ mul_self_pos.mpr <| show v 0 ^ 2 + v 1 ^ 2 ≠ 0 from fun h' => h <| by norm_num [ Complex.ext_iff, sq ] ; constructor <;> nlinarith ] ) ]
      ext i; fin_cases i <;> rfl
  use rot3_mat 2 ϕ * rot3_mat 1 (-θ)
  constructor
  · exact Submonoid.mul_mem _ (rot3_mat_mem_SO3 2 ϕ) (rot3_mat_mem_SO3 1 _)
  · simp only [rot3_mat]
    ext i; fin_cases i <;> simp [hθϕ, Matrix.mulVec] <;> ring

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
    have key : Mᵀ * M = 1 := by
      have h := hM.1.1; simp only [Matrix.star_eq_conjTranspose] at h; exact h
    simp only [v, Matrix.toEuclideanLin_apply, EuclideanSpace.norm_eq]
    -- The calculation (M*ᵥe)·(M*ᵥe) = e·((MᵀM)*ᵥe) = e·e = 1
    have hdot : (M *ᵥ ![0, 0, 1]) ⬝ᵥ (M *ᵥ ![0, 0, 1]) = 1 := by
      have : (M *ᵥ ![0, 0, 1]) ⬝ᵥ (M *ᵥ ![0, 0, 1]) =
             ![0, 0, 1] ⬝ᵥ ((Mᵀ * M) *ᵥ ![0, 0, 1]) := by
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.mul_apply,
          Matrix.transpose_apply]
        ring
      rw [this, key, Matrix.one_mulVec]
      simp [dotProduct, Fin.sum_univ_three]
    simp only [Real.sqrt_eq_one]
    have hsq : ∑ i, (M *ᵥ ![0, 0, 1]) i ^ 2 = 1 := by
      simp only [dotProduct, Fin.sum_univ_three] at hdot
      simp only [Fin.sum_univ_three, sq]
      convert hdot using 2
    simp only [Fin.sum_univ_three, sq] at hsq ⊢
    convert hsq using 2
    all_goals simp [Real.norm_eq_abs]
  -- Use spherical coordinates: v = [sin β cos α, sin β sin α, cos β]
  obtain ⟨β, α, hv_eq⟩ : ∃ β α : ℝ,
      (v : Fin 3 → ℝ) = ![Real.sin β * Real.cos α, Real.sin β * Real.sin α, Real.cos β] := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_three] at hv_norm ⊢
    use Real.arccos (v 2), Complex.arg (v 0 + v 1 * Complex.I)
    have h_cos_sin : Real.cos (Real.arccos (v 2)) = v 2 ∧
        Real.sin (Real.arccos (v 2)) = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
      rw [Real.cos_arccos, Real.sin_arccos] <;> try nlinarith
      exact ⟨rfl, congrArg Real.sqrt <| sub_eq_iff_eq_add.mpr hv_norm.symm⟩
    by_cases h : v 0 + v 1 * Complex.I = 0 <;> simp_all [Complex.cos_arg, Complex.sin_arg]
    · simp_all [Complex.ext_iff]
      ext i; fin_cases i <;> tauto
    · simp [Complex.normSq, Complex.norm_def] at *
      simp [← sq, mul_div_cancel₀ _
        (show √(v 0 ^ 2 + v 1 ^ 2) ≠ 0 from ne_of_gt <| Real.sqrt_pos.mpr <| by
          nlinarith [mul_self_pos.mpr <| show v 0 ^ 2 + v 1 ^ 2 ≠ 0 from fun h' => h <| by
            norm_num [Complex.ext_iff, sq]; constructor <;> nlinarith])]
      ext i; fin_cases i <;> rfl
  -- N = Ry(β) * Rz(-α) * M fixes [0,0,1]
  -- (First Rz(-α) removes azimuthal angle, then Ry(β) brings to z-axis)
  let N := Ry_mat β * Rz_mat (-α) * M
  have hN_SO3 : N ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (rot3_mat_mem_SO3 1 β) (rot3_mat_mem_SO3 2 (-α))) hM
  have hN_fixes_z : N.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1] := by
    -- Ry(β) * Rz(-α) * [sin β cos α, sin β sin α, cos β]
    -- Step 1: Rz(-α) * v = [sin β, 0, cos β]  (removes azimuthal angle)
    -- Step 2: Ry(β) * [sin β, 0, cos β] = [0, 0, 1]  (brings to z-axis)
    simp only [N, Matrix.mul_assoc, Matrix.toEuclideanLin_apply]
    have hv_sph : M *ᵥ ![0, 0, 1] =
        ![Real.sin β * Real.cos α, Real.sin β * Real.sin α, Real.cos β] := by
      ext i
      simp only [v, Matrix.toEuclideanLin_apply] at hv_eq
      exact congrFun hv_eq i
    -- Row access lemmas for explicit computation
    have Rz_row0 : Rz_mat (-α) 0 = ![Real.cos α, Real.sin α, 0] := by
      show ![Real.cos (-α), -Real.sin (-α), 0] = _
      simp only [Real.cos_neg, Real.sin_neg, neg_neg]
    have Rz_row1 : Rz_mat (-α) 1 = ![-Real.sin α, Real.cos α, 0] := by
      show ![Real.sin (-α), Real.cos (-α), 0] = _
      simp only [Real.cos_neg, Real.sin_neg]
    have Rz_row2 : Rz_mat (-α) 2 = ![0, 0, 1] := rfl
    have Ry_row0 : Ry_mat β 0 = ![Real.cos β, 0, -Real.sin β] := rfl
    have Ry_row1 : Ry_mat β 1 = ![0, 1, 0] := rfl
    have Ry_row2 : Ry_mat β 2 = ![Real.sin β, 0, Real.cos β] := rfl
    -- Step 1: After Rz(-α)
    have step1 : Rz_mat (-α) *ᵥ (M *ᵥ ![0, 0, 1]) = ![Real.sin β, 0, Real.cos β] := by
      rw [hv_sph]
      ext i
      fin_cases i
      · show (Rz_mat (-α) 0) ⬝ᵥ _ = _
        rw [Rz_row0]
        simp only [dotProduct, Fin.sum_univ_three]
        show Real.cos α * (Real.sin β * Real.cos α) +
             Real.sin α * (Real.sin β * Real.sin α) + 0 * Real.cos β = Real.sin β
        have h := Real.cos_sq_add_sin_sq α
        ring_nf
        linear_combination Real.sin β * h
      · show (Rz_mat (-α) 1) ⬝ᵥ _ = _
        rw [Rz_row1]
        simp only [dotProduct, Fin.sum_univ_three]
        show -Real.sin α * (Real.sin β * Real.cos α) +
             Real.cos α * (Real.sin β * Real.sin α) + 0 * Real.cos β = 0
        ring
      · show (Rz_mat (-α) 2) ⬝ᵥ _ = _
        rw [Rz_row2]
        simp only [dotProduct, Fin.sum_univ_three]
        show 0 * (Real.sin β * Real.cos α) +
             0 * (Real.sin β * Real.sin α) + 1 * Real.cos β = Real.cos β
        ring
    -- Step 2: After Ry(β)
    have step2 : Ry_mat β *ᵥ ![Real.sin β, 0, Real.cos β] = ![(0:ℝ), 0, 1] := by
      ext i
      fin_cases i
      · show (Ry_mat β 0) ⬝ᵥ _ = _
        rw [Ry_row0]
        simp only [dotProduct, Fin.sum_univ_three]
        show Real.cos β * Real.sin β + 0 * 0 + (-Real.sin β) * Real.cos β = 0
        ring
      · show (Ry_mat β 1) ⬝ᵥ _ = _
        rw [Ry_row1]
        simp only [dotProduct, Fin.sum_univ_three]
        show 0 * Real.sin β + 1 * 0 + 0 * Real.cos β = 0
        ring
      · show (Ry_mat β 2) ⬝ᵥ _ = _
        rw [Ry_row2]
        simp only [dotProduct, Fin.sum_univ_three]
        show Real.sin β * Real.sin β + 0 * 0 + Real.cos β * Real.cos β = 1
        have h := Real.sin_sq_add_cos_sq β
        ring_nf
        linear_combination h
    -- Combine: use the steps to compute N * [0,0,1]
    have h_calc : (Ry_mat β * (Rz_mat (-α) * M)) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
      -- Use: (A * B) *ᵥ x = A *ᵥ (B *ᵥ x) by ← mulVec_mulVec
      calc (Ry_mat β * (Rz_mat (-α) * M)) *ᵥ ![0, 0, 1]
          = Ry_mat β *ᵥ ((Rz_mat (-α) * M) *ᵥ ![0, 0, 1]) := by
              rw [← Matrix.mulVec_mulVec]
        _ = Ry_mat β *ᵥ (Rz_mat (-α) *ᵥ (M *ᵥ ![0, 0, 1])) := by
              rw [← Matrix.mulVec_mulVec]
        _ = Ry_mat β *ᵥ ![Real.sin β, 0, Real.cos β] := by
              rw [step1]
        _ = ![0, 0, 1] := step2
    simp only [h_calc]
  -- By SO3_fixing_z_is_Rz, N = Rz(γ) for some γ
  obtain ⟨γ, hγ⟩ := SO3_fixing_z_is_Rz N hN_SO3 hN_fixes_z
  -- Therefore M = Rz(α) * Ry(-β) * Rz(γ)
  -- N = Ry(β) * Rz(-α) * M, so M = Rz(α) * Ry(-β) * N = Rz(α) * Ry(-β) * Rz(γ)
  use α, -β, γ
  -- From N = Ry_mat β * Rz_mat (-α) * M (definition of N) and hγ : N = Rz_mat γ
  -- We get: Rz_mat γ = Ry_mat β * Rz_mat (-α) * M
  -- Multiply on left by Ry_mat (-β): Ry_mat (-β) * Rz_mat γ = Rz_mat (-α) * M
  -- Multiply on left by Rz_mat α: Rz_mat α * Ry_mat (-β) * Rz_mat γ = M
  have h1 : Rz_mat γ = Ry_mat β * Rz_mat (-α) * M := hγ ▸ rfl
  have h2 : Ry_mat (-β) * Rz_mat γ = Rz_mat (-α) * M := by
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, neg_Ry_mat_mul, Matrix.one_mul]
  calc M = Rz_mat α * (Rz_mat (-α) * M) := by
           rw [← Matrix.mul_assoc, Rz_mat_mul_neg, Matrix.one_mul]
       _ = Rz_mat α * (Ry_mat (-β) * Rz_mat γ) := by rw [h2]
       _ = Rz_mat α * Ry_mat (-β) * Rz_mat γ := by rw [Matrix.mul_assoc]

/-- Rz(0) = 1. -/
@[simp]
lemma Rz_mat_zero : Rz_mat 0 = 1 := by simp [Rz_mat, Matrix.one_fin_three]

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

-- TODO something like this really ought to exist in mathlib.
lemma specialOrthogonalGroup_mem_inv {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (U_SO3 : U ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    U⁻¹ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  have h_inv : U * U.transpose = 1 ∧ U.transpose * U = 1 := by
    have h_ortho : U * U.transpose = 1 := U_SO3.1.2
    have h_ortho' : U.transpose * U = 1 := by rw [← mul_eq_one_comm, h_ortho]
    exact ⟨h_ortho, h_ortho'⟩
  have h_inv : U⁻¹ = U.transpose := by
    rw [Matrix.inv_eq_right_inv h_inv.1]
  simp_all only [Matrix.mem_specialOrthogonalGroup_iff, Matrix.det_transpose, and_true]
  constructor <;> aesop

lemma SO3_is_conj_Rz (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (_ : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (γ : ℝ), A = U * Rz_mat γ * U⁻¹ := by
  obtain ⟨w, _⟩ := SO3_has_eigenvalue_one A hA
  let v := ‖w‖⁻¹ • w
  have A_fixes_v : A *ᵥ v = v := by
    have : (A.toEuclideanLin v).ofLp = v.ofLp := by simp_all [v]
    simpa [Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply]
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
  rw [mul_assoc, Matrix.mul_nonsing_inv U U_det_unit, mul_one]

lemma Rz_mod_two_pi (γ : ℝ) : ∃ γ' ∈ Set.Ioc (-π) π, Rz_mat γ = Rz_mat γ' := by
  use π - Real.emod (π - γ) (2 * π)
  refine ⟨?_, ?_⟩
  · have := Real.emod_in_interval (a := π - γ) (b := 2 * π) two_pi_pos
    grind
  · obtain ⟨k, hk⟩ := Real.emod_exists_multiple (π - γ) (2 * π) two_pi_pos
    rw [hk]
    convert_to Rz_mat γ = Rz_mat (γ + (↑(-k) : ℝ) * (2 * π))
    · push_cast; ring_nf
    rw [Rz_mat_add_int_mul_two_pi (-k) γ]

lemma SO3_is_conj_Rz_within_pi (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (_ : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (γ : ℝ),
      γ ∈ Set.Ioc (-π) π ∧ A = U * Rz_mat γ * U⁻¹ := by
  obtain ⟨U, U_SO, γ, hγ⟩ := SO3_is_conj_Rz A hA
  obtain ⟨γ', γ'_in, hγ'⟩ := Rz_mod_two_pi γ
  use U, U_SO, γ', γ'_in, hγ'▸hγ

end AristotleLemmas

def Matrix.OrthogonalGroup.toLinearEquiv {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ)
    : Euc(n) ≃ₗ[ℝ] Euc(n) :=
  WithLp.linearEquiv 2 ℝ (Fin n → ℝ) ≪≫ₗ
    Matrix.UnitaryGroup.toLinearEquiv A ≪≫ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm

lemma Matrix.orthogonalGroup.to_linear_equiv_apply {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Euc(n)) :
    Matrix.OrthogonalGroup.toLinearEquiv A x = A.1.mulVec x := by
  rfl

lemma to_euc_mul {a b c : ℕ}
    (u : Euc(a) →ₗ[ℝ] Euc(b)) (v : Euc(b) →ₗ[ℝ] Euc(c)) :
    Matrix.toEuclideanLin.symm v * Matrix.toEuclideanLin.symm u =
    Matrix.toEuclideanLin.symm (v ∘ₗ u) := by
  refine LinearEquiv.injective Matrix.toEuclideanLin ?_
  have (uu : Matrix (Fin b) (Fin a) ℝ) (vv : Matrix (Fin c) (Fin b) ℝ) :
     Matrix.toEuclideanLin (vv * uu) = Matrix.toEuclideanLin vv ∘ₗ Matrix.toEuclideanLin uu := by
    ext x
    simp only [Matrix.toEuclideanLin_apply, LinearMap.coe_comp, Function.comp_apply,
      Matrix.mulVec_mulVec]
  rw [this]
  simp

lemma to_euc_one {n : ℕ} : Matrix.toEuclideanLin.symm (LinearMap.id (M := Euc(n))) = 1 := by
  ext i j
  rw [Matrix.toEuclideanLin]
  simp only [LinearEquiv.trans_symm, Matrix.toLin'_symm, LinearEquiv.trans_apply, LinearMap.toMatrix'_apply]
  rfl

lemma inv_euclidean_eq_euclidean_symm (u : Euc(3) ≃ₗ[ℝ] Euc(3)) :
    (Matrix.toEuclideanLin.symm u.toLinearMap)⁻¹ = Matrix.toEuclideanLin.symm u.symm.toLinearMap := by
  rw [Matrix.inv_eq_right_inv]
  rw [to_euc_mul u.symm.toLinearMap u.toLinearMap]
  simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap]
  exact to_euc_one

lemma euclidean_linear_equiv_inverse (v : ℝ³) (u : Euc(3) ≃ₗ[ℝ] Euc(3)) (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hu : U = Matrix.toEuclideanLin.symm u.toLinearMap) :
    u.symm v = WithLp.toLp 2 (U⁻¹.mulVec v) := by
  rw [hu, inv_euclidean_eq_euclidean_symm]
  have (qq : Euc(3) ≃ₗ[ℝ] Euc(3)) : ((Matrix.toEuclideanLin.symm (qq.toLinearMap)).toEuclideanLin v) =
      (Matrix.toEuclideanLin.symm (qq.toLinearMap)).mulVec v := by rfl
  simp only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_coe] at this
  specialize this u.symm
  have xx : WithLp.toLp 2 ((u.symm v).ofLp) =
      WithLp.toLp 2 ((Matrix.toEuclideanLin.symm ↑u.symm).mulVec v.ofLp) := by
    congr
  simpa using xx

lemma rot3_rot3_orth_equiv_rotz {d d' : Fin 3} {α β : ℝ} :
    ∃ (u : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (γ : ℝ), γ ∈ Set.Ioc (-π) π ∧
    rot3 d α ∘L rot3 d' β =
      u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap := by
  have dd'_so3 : rot3_mat d α * rot3_mat d' β ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (Bounding.rot3_mat_mem_SO3 d α) (Bounding.rot3_mat_mem_SO3 d' β)

  obtain ⟨ U, hU, γ, hγ, h ⟩ := SO3_is_conj_Rz_within_pi ( rot3_mat d α * rot3_mat d' β ) dd'_so3
  -- Let $u$ be the linear isometry equivalence corresponding to $U$.
  obtain ⟨u, hu⟩ : ∃ u : Euc(3) ≃ₗᵢ[ℝ] Euc(3), ∀ x : Euc(3), u x = U.mulVec x := by
    have hU_orthogonal : U.transpose * U = 1 := hU.1
    refine ⟨ { Matrix.OrthogonalGroup.toLinearEquiv ⟨U, hU⟩ with norm_map' := ?_ },
               Matrix.orthogonalGroup.to_linear_equiv_apply ⟨U, hU⟩ ⟩
    simp_all [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    -- Since $U$ is orthogonal, we have $U^T U = I$, which implies that $U$ preserves the dot product.
    have hU_dot : ∀ x y : Euc(3), dotProduct (U.mulVec x) (U.mulVec y) = dotProduct x y := by
      simp_all [Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
    simp_all only [dotProduct, Fin.sum_univ_three, Fin.isValue]
    intro x
    exact congr_arg Real.sqrt ( by simpa only [ sq ] using hU_dot x x )
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
  · have : U = Matrix.toEuclideanLin.symm u.toLinearMap := by
      suffices h : Matrix.toEuclideanLin U = u.toLinearMap from
        (LinearEquiv.eq_symm_apply Matrix.toEuclideanLin).mpr h
      ext1 x
      specialize hu x
      rw [show U.mulVec x.ofLp = (Matrix.toEuclideanLin U) x by simp] at hu
      exact WithLp.ofLp_injective 2 hu |>.symm
    rw [show ∀ x : Euc(3), u.symm x = WithLp.toLp 2 (U⁻¹.mulVec x) from
      fun x => euclidean_linear_equiv_inverse x u U this]
    simp [RzL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp [Matrix.mul_apply]
    simp [Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Matrix.vecMul]
    ring_nf
