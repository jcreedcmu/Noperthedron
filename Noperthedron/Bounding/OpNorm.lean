module

public import Noperthedron.Basic

@[expose] public section

namespace Bounding

open scoped Matrix
open scoped RealInnerProductSpace

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

noncomputable def OrthogonalGroup.toLinearEquiv {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ)
    : Euc(n) ≃ₗ[ℝ] Euc(n) :=
  WithLp.linearEquiv 2 ℝ (Fin n → ℝ) ≪≫ₗ
    Matrix.UnitaryGroup.toLinearEquiv A ≪≫ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm

lemma OrthogonalGroup.toLinearEquiv_apply {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Euc(n)) :
    OrthogonalGroup.toLinearEquiv A x = A.1.mulVec x := by
  rfl

/-- An orthogonal matrix gives a linear isometry equivalence of Euclidean space. -/
noncomputable def OrthogonalGroup.toLinearIsometryEquiv {n : ℕ}
    (A : Matrix.orthogonalGroup (Fin n) ℝ) : Euc(n) ≃ₗᵢ[ℝ] Euc(n) :=
  (OrthogonalGroup.toLinearEquiv A).isometryOfInner fun x y => by
    have hA : A.1ᵀ * A.1 = 1 := A.2.1
    have key : (A.1 *ᵥ x) ⬝ᵥ (A.1 *ᵥ y) = x ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hA, Matrix.vecMul_one]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      OrthogonalGroup.toLinearEquiv_apply]
    simpa [dotProduct, mul_comm] using key

lemma OrthogonalGroup.toLinearIsometryEquiv_apply {n : ℕ}
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Euc(n)) :
    OrthogonalGroup.toLinearIsometryEquiv A x = A.1.mulVec x :=
  OrthogonalGroup.toLinearEquiv_apply A x

theorem Rz_preserves_norm (α : ℝ) (v : ℝ³) : ‖RzL α v‖ = ‖v‖ :=
  (OrthogonalGroup.toLinearIsometryEquiv ⟨rot3_mat 2 α, rot3_mat_mem_O3 2 α⟩).norm_map v

end Bounding

end
