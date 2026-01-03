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
  fin_cases d <;>
  · constructor
    · apply rot3_mat_mem_O3
    · simp [rot3_mat, Rx_mat, Ry_mat, Rz_mat, Matrix.det_fin_three, ←sq]

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
      obtain ⟨v, v_nz, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (show (A - 1).det = 0 by linarith)
      exact ⟨WithLp.toLp 2 v, by simpa using v_nz, by simpa [sub_eq_zero, Matrix.sub_mulVec] using hv⟩

lemma SO3_fixing_z_is_Rz (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hAz : A.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1]) :
    ∃ γ, γ ∈ Set.Ioc (-π) π ∧ A = Rz_mat γ := by
  rcases hA with ⟨hA₁, hA₂⟩
  simp_all [Matrix.mem_unitaryGroup_iff]
  -- Since $A$ is in $SO(3)$ and fixes the $z$-axis, its matrix representation must be of the form $\begin{pmatrix} \cos \gamma & -\sin \gamma & 0 \\ \sin \gamma & \cos \gamma & 0 \\ 0 & 0 & 1 \end{pmatrix}$ for some $\gamma$.
  -- Since A is in SO(3) and fixes the z-axis, the third row and column must be [0, 0, 1]. Therefore, A can be written as [[a, b, 0], [c, d, 0], [0, 0, 1]].
  obtain ⟨a, b, c, d, hA⟩ : ∃ a b c d : ℝ, A = !![a, b, 0; c, d, 0; 0, 0, 1] := by
    -- Since A fixes the z-axis, the third column of A must be [0, 0, 1].
    have h_third_col : A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 2 2 = 1 := by
      -- By definition of matrix multiplication, the third column of A is the image of the vector (0,0,1) under A.
      have h_third_col : A.mulVec ![0, 0, 1] = ![0, 0, 1] := by
        convert hAz
      simp [ ← List.ofFn_inj, Matrix.mulVec ] at h_third_col
      aesop
    simp_all [ ← Matrix.ext_iff, Fin.forall_fin_succ ]
    simp_all [ Matrix.mul_apply, Fin.sum_univ_three ]
    exact mul_self_add_mul_self_eq_zero.mp hA₁.2.2.2.2
  -- Since A is in SO(3), we have a^2 + b^2 = 1 and c^2 + d^2 = 1, and ad - bc = 1.
  have h_conditions : a^2 + b^2 = 1 ∧ c^2 + d^2 = 1 ∧ a * d - b * c = 1 := by
    simp_all [← Matrix.ext_iff, Fin.forall_fin_succ]
    simp_all [Matrix.vecMul, Matrix.det_fin_three]
    exact ⟨by linarith, by linarith⟩
  -- Since $a^2 + b^2 = 1$ and $c^2 + d^2 = 1$, we can write $a = \cos \gamma$ and $b = -\sin \gamma$ for some $\gamma$.
  obtain ⟨γ, hγ, hγa, hγb⟩ : ∃ γ : ℝ, γ ∈ Set.Ioc (-π) π ∧
      a = Real.cos γ ∧ b = -Real.sin γ := by
    refine ⟨Complex.arg (a + (-b) * Complex.I), Complex.arg_mem_Ioc _, ?_⟩
    rw [Complex.cos_arg, Complex.sin_arg] <;> simp [Complex.ext_iff]
    · simp [Complex.normSq, Complex.norm_def, ← sq, h_conditions]
    · aesop
  -- Since $c = \sin \gamma$ and $d = \cos \gamma$, we can substitute these into the matrix.
  have ⟨hc, hd⟩ : c = Real.sin γ ∧ d = Real.cos γ := by grind
  use γ, hγ
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
        · simp_all [ Complex.ext_iff ]
          ext i; fin_cases i <;> tauto
        · simp [Complex.normSq, Complex.norm_def] at *
          norm_num [← sq, mul_div_cancel₀ _ (show √( v 0 ^ 2 + v 1 ^ 2 ) ≠ 0 from ne_of_gt <| Real.sqrt_pos.mpr <| by nlinarith [ mul_self_pos.mpr <| show v 0 ^ 2 + v 1 ^ 2 ≠ 0 from fun h' => h <| by norm_num [ Complex.ext_iff, sq ] ; constructor <;> nlinarith ] ) ]
          ext i; fin_cases i <;> rfl
      -- Let $U$ be the rotation matrix that rotates the $z$-axis to $v$. We can construct such a matrix using the Rodrigues' rotation formula.
      use !![Real.cos ϕ, -Real.sin ϕ, 0; Real.sin ϕ, Real.cos ϕ, 0; 0, 0, 1] *
          !![Real.cos θ, 0, Real.sin θ; 0, 1, 0; -Real.sin θ, 0, Real.cos θ]
      constructor
      · constructor
        · constructor
          · ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Fin.sum_univ_succ ] <;> ring_nf;
            · rw [Real.sin_sq, Real.sin_sq]; ring
            · rw [Real.sin_sq]; ring
            · norm_num
            · rw [Real.sin_sq]; ring
            · simp only [Real.sin_sq]; ring
          · ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Fin.sum_univ_succ ] <;> ring_nf;
            · rw [ Real.sin_sq, Real.sin_sq ]; ring
            · rw [ Real.sin_sq ]; ring
            · rw [ Real.sin_sq ]; ring
            · rw [ Real.sin_sq, Real.sin_sq ]; ring
            · simp
        · -- The determinant of the product of two matrices is the product of their determinants.
          simp [Matrix.det_fin_three]
          nlinarith [Real.sin_sq_add_cos_sq ϕ, Real.sin_sq_add_cos_sq θ]
      · ext i; fin_cases i <;> norm_num [ hθϕ, Matrix.mulVec ] <;> ring

lemma SO3_is_conj_Rz (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (_ : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (γ : ℝ),
      γ ∈ Set.Ioc (-π) π ∧ A = U * Rz_mat γ * U⁻¹ := by
        -- Let $v$ be an eigenvector of $A$ corresponding to the eigenvalue $1$.
        obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 ∧ A.toEuclideanLin v = v ∧ ‖v‖ = 1 := by
          obtain ⟨v, hv⟩ := SO3_has_eigenvalue_one A hA
          refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩ <;> simp_all [norm_smul]
        -- Let $U$ be an element of $SO(3)$ that maps $v$ to the z-axis.
        obtain ⟨U, hU⟩ := exists_SO3_mulVec_ez_eq v hv.2.2
        -- Let $B = U^{-1} A U$. Then $B$ is also in $SO(3)$ and fixes the z-axis.
        set B : Matrix (Fin 3) (Fin 3) ℝ := U⁻¹ * A * U
        have hB : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ B.mulVec ![0, 0, 1] = ![0, 0, 1] := by
          apply And.intro
          · simp_all only [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
            simp +zetaDelta at *
            simp_all [ Matrix.mul_assoc, Matrix.inv_eq_right_inv hU.1.1 ]
            simp_all [ ← Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp hU.1.1 ]
          · have hB : A.mulVec v = v := by
              obtain ⟨_, hv', _⟩ := hv
              convert hv'
              · rw [WithLp.toLp.injEq]; simp
            have hB : U⁻¹.mulVec (A.mulVec (U.mulVec ![0, 0, 1])) = U⁻¹.mulVec (U.mulVec ![0, 0, 1]) := by
              aesop;
            convert hB using 1 <;> simp
            · rw [← Matrix.mul_assoc]
            · rw [Matrix.nonsing_inv_mul _]
              · simp
              · have q : U.det = 1 := hU.1.2
                simp [q, isUnit_iff_ne_zero, ne_eq]
        -- Since $B$ fixes the z-axis, there exists $\gamma \in [-\pi, \pi)$ such that $B = R_z(\gamma)$.
        obtain ⟨γ, hγ⟩ : ∃ γ ∈ Set.Ioc (-Real.pi) Real.pi, B = Rz_mat γ := by
          -- Since $B$ fixes the z-axis, there exists $\gamma \in [-\pi, \pi)$ such that $B = Rz_mat \gamma$ by the properties of SO(3).
          apply SO3_fixing_z_is_Rz B hB.left
          · obtain ⟨_, hB'⟩ := hB
            convert hB'; simp
        refine ⟨ U, ?_, γ, hγ.1, ?_⟩
        · exact hU.1.1
        · simp +zetaDelta at *
          rw [← hγ.2]
          simp only [← mul_assoc]
          exact hU.1.1 |> fun h => by simp_all [Matrix.mem_specialOrthogonalGroup_iff]


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
  have xx : WithLp.toLp 2 ((u.symm v).ofLp) = WithLp.toLp 2 ((Matrix.toEuclideanLin.symm ↑u.symm).mulVec v.ofLp) := by
    congr
  simpa using xx

lemma rot3_rot3_orth_equiv_rotz {d d' : Fin 3} {α β : ℝ} :
    ∃ (u : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (γ : ℝ), γ ∈ Set.Ioc (-π) π ∧
    rot3 d α ∘L rot3 d' β =
      u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap := by
  have := Bounding.SO3_is_conj_Rz ( rot3_mat d α * rot3_mat d' β ) ?_
  · obtain ⟨ U, hU, γ, hγ, h ⟩ := this
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
    simp [hu, Matrix.mulVec]
    convert congr_fun ( congr_arg ( fun m => m.mulVec x ) h ) ‹_› using 1
    · have h_expand : ∀ (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : Euc(3)),
                        (A.toEuclideanLin (B.toEuclideanLin x)) = (A * B).mulVec x := by
        simp
      convert congr_fun (h_expand ( rot3_mat d α ) ( rot3_mat d' β ) x) ‹_› using 1
      fin_cases d <;> fin_cases d' <;> rfl;
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
  · exact Submonoid.mul_mem _ (Bounding.rot3_mat_mem_SO3 d α) (Bounding.rot3_mat_mem_SO3 d' β)
