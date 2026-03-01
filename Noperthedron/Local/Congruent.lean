import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Invertible
import Mathlib.Analysis.InnerProductSpace.LinearMap

import Noperthedron.Basic
import Noperthedron.Local.EpsSpanning

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

def Triangle.toMatrix (P : Local.Triangle) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => P j i

@[simp]
lemma Triangle.toMatrix_col (P : Local.Triangle) (j : Fin 3) : P.toMatrix.col j = P j := rfl

def Triangle.toSymMatrix (P : Local.Triangle) : Matrix (Fin 3) (Fin 3) ℝ :=
  (P.toMatrix.transpose) * P.toMatrix

@[simp]
lemma Triangle.toSymMatrix_apply (P : Triangle) (i j : Fin 3) :
    P.toSymMatrix i j = ⟪P j, P i⟫ := by
  simp [Triangle.toSymMatrix, Triangle.toMatrix, Matrix.mul_apply, Fin.sum_univ_three,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]

/--
[SY25] Lemma 35
-/
lemma congruent_iff_sym_matrix_eq (P Q : Triangle) (hQ : Invertible (Q.toMatrix)) :
    P.Congruent Q ↔ (P.toSymMatrix = Q.toSymMatrix) := by
  constructor
  · rintro ⟨L, hL⟩
    ext i j
    simp [Triangle.toSymMatrix_apply, hL, LinearIsometry.inner_map_map]
  · intro hSym
    classical
    have hSym' : P.toMatrixᵀ * P.toMatrix = Q.toMatrixᵀ * Q.toMatrix := by
      simpa [Triangle.toSymMatrix] using hSym
    -- Candidate orthogonal matrix `A := P * Q⁻¹`.
    let A : Matrix (Fin 3) (Fin 3) ℝ := P.toMatrix * ⅟ Q.toMatrix
    have hA : Aᵀ * A = 1 := by
      calc
        Aᵀ * A
            = (⅟ Q.toMatrix)ᵀ * (P.toMatrixᵀ * P.toMatrix) * (⅟ Q.toMatrix) := by
                simp [A, Matrix.transpose_mul, Matrix.mul_assoc]
        _   = (⅟ Q.toMatrix)ᵀ * (Q.toMatrixᵀ * Q.toMatrix) * (⅟ Q.toMatrix) := by
                simp [hSym', Matrix.mul_assoc]
        _   = ((⅟ Q.toMatrix)ᵀ * Q.toMatrixᵀ) * (Q.toMatrix * ⅟ Q.toMatrix) := by
                simp [Matrix.mul_assoc]
        _   = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
                have h1 : (⅟ Q.toMatrix)ᵀ * Q.toMatrixᵀ = (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
                  invOf_mul_self (a := Q.toMatrixᵀ)
                rw [h1, mul_invOf_self, one_mul]
    -- Bundle `A` as a linear isometry.
    let f : Euc(3) →ₗ[ℝ] Euc(3) := A.toEuclideanLin
    have hf_inner : ∀ x y : Euc(3), ⟪f x, f y⟫ = ⟪x, y⟫ := by
      intro x y
      simp [f, EuclideanSpace.inner_eq_star_dotProduct]
      -- goal: `A *ᵥ y.ofLp ⬝ᵥ A *ᵥ x.ofLp = y.ofLp ⬝ᵥ x.ofLp`
      calc
        A *ᵥ y.ofLp ⬝ᵥ A *ᵥ x.ofLp
            = (A *ᵥ y.ofLp) ᵥ* A ⬝ᵥ x.ofLp := Matrix.dotProduct_mulVec _ _ _
        _   = y.ofLp ᵥ* (Aᵀ * A) ⬝ᵥ x.ofLp := by
                simpa using congrArg (fun t => t ⬝ᵥ x.ofLp)
                  (Matrix.vecMul_mulVec (A := A) (B := A) (x := y.ofLp))
        _   = y.ofLp ⬝ᵥ x.ofLp := by
                simp [hA]
    let L : Euc(3) →ₗᵢ[ℝ] Euc(3) := f.isometryOfInner hf_inner
    refine ⟨L, ?_⟩
    intro i
    -- Use `A * Q = P` to show `L (Q i) = P i`.
    have hAQ : A * Q.toMatrix = P.toMatrix := by
      simp [A, Matrix.mul_assoc]
    have h_mulVec : A *ᵥ (Q.toMatrix.col i) = P.toMatrix.col i := by
      calc
        A *ᵥ (Q.toMatrix.col i)
            = (A * Q.toMatrix).col i := by
                -- `A *ᵥ col i = (A * Q).col i`
                simpa [Matrix.mulVec_single_one] using
                  (Matrix.mulVec_mulVec (v := Pi.single i 1) (M := A) (N := Q.toMatrix))
        _   = P.toMatrix.col i := by
                simp [hAQ]
    have h_mulVec' : A *ᵥ (Q i).ofLp = (P i).ofLp := by
      simpa [Triangle.toMatrix_col] using h_mulVec
    ext j
    have : (L (Q i)).ofLp = (P i).ofLp := by simp [L, f, h_mulVec']
    exact (congrFun this j).symm
