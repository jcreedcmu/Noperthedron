import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Noperthedron.Local.EpsSpanning
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.Lemma42
import Noperthedron.RationalApprox.MatrixBounds

namespace RationalApprox

open scoped RealInnerProductSpace Real
open scoped Matrix


/-- [SY25] Definition 45. Note that the "+ 1" at the type Fin 3 wraps.
  We don't include in this definition the constraint that θ, φ ∈ [-4, 4] or
  that ‖P₁‖, ‖P₂‖, ‖P₃‖ ≤ 1 + κ.
  If a user of this code wants to impose those, they'll have to separately. -/
/- QUESTION: should be we be casting to ℝ to take the inner product?;
   on the one hand, we don't *have* to, because rotR (π / 2) is a valid 90° rotation on rationals.
   And should ε be real or rational? -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℝ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) + 6 * κ <
      ⟪rotR (π / 2) (rotMℚ θ φ (P i)), rotMℚ θ φ (P (i + 1))⟫

def κApproxTri (A : Local.Triangle) (A' : RationalApprox.Triangle) : Prop :=
  ∀ i, ‖A i - (↑(A' i) : ℝ³)‖ ≤ κ

@[simp]
lemma norm_transpose_euc_lin {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) :
    ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  calc ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖
  _ = ‖Mᴴ.toEuclideanLin.toContinuousLinearMap‖ := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  _ = ‖M.toEuclideanLin.adjoint.toContinuousLinearMap‖ := by rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  _ = ‖M.toEuclideanLin.toContinuousLinearMap.adjoint‖ := rfl
  _ = ‖M.toEuclideanLin.toContinuousLinearMap‖ := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _

def matOfVec {n : ℕ} (v : Euc(n)) : Matrix (Fin 1) (Fin n) ℝ := fun _ii jj => v jj
def matOfCovec {n : ℕ} (v : Euc(n)) : Matrix (Fin n) (Fin 1) ℝ := fun ii _jj => v ii

noncomputable
def mapOfVec {n : ℕ} (v : Euc(n)) : Euc(n) →L[ℝ] Euc(1) := matOfVec v |>.toEuclideanLin.toContinuousLinearMap
noncomputable
def mapOfCovec {n : ℕ} (v : Euc(n)) : Euc(1) →L[ℝ] Euc(n) := matOfCovec v |>.toEuclideanLin.toContinuousLinearMap

@[simp]
lemma norm_map_vec_eq_norm_vec {n : ℕ} (v : Euc(n)) : ‖mapOfVec v‖ = ‖v‖ := by
  sorry

@[simp]
lemma norm_map_covec_eq_norm_vec {n : ℕ} (v : Euc(n)) : ‖mapOfCovec v‖ = ‖v‖ := by
  sorry

lemma bound_rotM (θ φ : ℝ) : ‖rotM θ φ‖ ≤ 1 + κ := by
  norm_num [Bounding.rotM_norm_one, κ]

lemma bound_rotR (α : ℝ) : ‖rotR α‖ ≤ 1 := by exact le_of_eq (Bounding.rotR_norm_one α)

/- [SY25 Lemma 46] -/
theorem ek_spanning_imp_e_spanning (P : Local.Triangle) (P' : RationalApprox.Triangle)
    (hk : κApproxTri P P') {θ φ ε : ℝ}
    (hθ : θ ∈ Set.Icc (-4) 4) (hφ : φ ∈ Set.Icc (-4) 4)
    (hspan : P'.Spanning θ φ ε) : P.Spanning θ φ ε := by
  constructor
  · exact hspan.pos
  · have lt := hspan.lt
    intro i
    suffices h : |⟪(rotR (π / 2)) (rotM θ φ (P i)),  rotM θ φ (P (i + 1))⟫
                 - ⟪(rotR (π / 2)) (rotMℚ θ φ (P' i)), rotMℚ θ φ (P' (i + 1))⟫| ≤ 6 * κ by
      calc ⟪(rotR (π / 2)) ((rotM θ φ) (P i)), (rotM θ φ) (P (i + 1))⟫
      _ ≥ ⟪(rotR (π / 2)) (rotMℚ θ φ (P' i)), rotMℚ θ φ (P' (i + 1))⟫ - 6 * κ :=
        sub_le_of_abs_sub_le_left h
      _ > 2 * ε * (√2 + ε) := lt_tsub_of_add_lt_right (hspan.lt i)

    -- (A) P (i + 1)ᵀ ∘ (rotM θ φ)ᵀ ∘ rotR (π / 2) ∘ rotM θ φ ∘ P i
    -- (B) P' (i + 1)ᵀ ∘ (rotMℚ θ φ)ᵀ ∘ rotR (π / 2) ∘ rotMℚ θ φ ∘ P' i
    let mv := ⟦
      mapOfVec (P i),
      mapOfVec (P' i),
      (rotM_mat θ φ)ᵀ.toEuclideanLin.toContinuousLinearMap,
      (rotMℚ_mat θ φ)ᵀ.toEuclideanLin.toContinuousLinearMap,
      rotR (π / 2), rotR (π / 2),
      rotM θ φ,
      rotMℚ θ φ,
      mapOfCovec (P i),
      mapOfCovec (P' i)
    ⟧

    have bound_P (i : Fin 3) : ‖P i‖ ≤ 1 + κ := by
      sorry
    have bound_P' (i : Fin 3) : ‖WithLp.toLp 2 fun x ↦ ↑((P' i).ofLp x)‖ ≤ 1 + κ := by
      sorry
    have hmvs : mv.size = 5 := by simp [mv]
    have hanb : MatVec.allNormsBelow mv [1 + κ, 1 + κ, 1, 1 + κ, 1 + κ] := by
      simp only [MatVec.allNormsBelow, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, MatVec.allNormsBelow.go, true_and, and_self, mv, norm_transpose_euc_lin,
        norm_map_vec_eq_norm_vec, norm_map_covec_eq_norm_vec]
      exact ⟨⟨⟨⟨
        ⟨bound_P' i, bound_P i⟩,
        ⟨Mℚ_norm_bounded hθ hφ, bound_rotM θ φ⟩⟩, bound_rotR (π / 2)⟩,
        ⟨Mℚ_norm_bounded hθ hφ, bound_rotM θ φ⟩⟩, ⟨bound_P' i, bound_P i⟩⟩
    have hva : ⟪(rotR (π / 2)) ((rotM θ φ) (P i)), (rotM θ φ) (P (i + 1))⟫ = mv.valA := by
      simp [MatVec.valA, mv, MatVec.compA]
      sorry
    have hvb : ⟪(rotR (π / 2)) (rotMℚ θ φ (P' i)), rotMℚ θ φ (P' (i + 1))⟫ = mv.valB := by
      simp [MatVec.valB, mv, MatVec.compB]
      sorry
    have hdbb : mv.DiffBoundedBy κ := by
      simp [MatVec.DiffBoundedBy, mv]
      clear hvb hva hanb hmvs mv
      split_ands
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
    suffices h : |mv.valA - mv.valB| ≤ 6 * κ by simpa [hva, hvb] using h
    grw [norm_sub_le_bound1 mv κ (by norm_num [κ]) hdbb hanb]
    rw [hmvs]
    norm_num [κ]
