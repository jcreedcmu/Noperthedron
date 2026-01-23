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

private lemma matOfCovec_transpose {n : ℕ} (v : Euc(n)) : (matOfCovec v)ᵀ = matOfVec v := by
  ext i j
  simp [matOfVec, matOfCovec]

private lemma mapOfCovec_apply {n : ℕ} (v : Euc(n)) (c : Euc(1)) : mapOfCovec v c = c 0 • v := by
  ext i
  simp [mapOfCovec, matOfCovec, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, mul_comm]

private lemma Euc1_norm_eq (c : Euc(1)) : ‖c‖ = |c 0| := by
  simpa [EuclideanSpace.norm_eq] using Real.sqrt_sq_eq_abs _

@[simp]
lemma norm_map_covec_eq_norm_vec {n : ℕ} (v : Euc(n)) : ‖mapOfCovec v‖ = ‖v‖ := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg v) (fun c ↦ ?_) (fun N _ hN ↦ ?_)
  · simp [mapOfCovec_apply, norm_smul, Euc1_norm_eq, mul_comm]
  · simpa [mapOfCovec_apply, EuclideanSpace.norm_single] using hN (EuclideanSpace.single 0 1)

@[simp]
lemma norm_map_vec_eq_norm_vec {n : ℕ} (v : Euc(n)) : ‖mapOfVec v‖ = ‖v‖ := by
  change ‖(matOfCovec v)ᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖v‖
  rw [norm_transpose_euc_lin]
  exact norm_map_covec_eq_norm_vec v

lemma bound_rotM (θ φ : ℝ) : ‖rotM θ φ‖ ≤ 1 + κ := by
  norm_num [Bounding.rotM_norm_one, κ]

lemma bound_rotR (α : ℝ) : ‖rotR α‖ ≤ 1 := by exact le_of_eq (Bounding.rotR_norm_one α)

private lemma matOfVec_sub {n : ℕ} (v w : Euc(n)) : matOfVec v - matOfVec w = matOfVec (v - w) := by
  ext i j; simp [matOfVec]

private lemma matOfCovec_sub {n : ℕ} (v w : Euc(n)) : matOfCovec v - matOfCovec w = matOfCovec (v - w) := by
  ext i j; simp [matOfCovec]

private lemma norm_mapOfVec_sub_le {n : ℕ} (v w : Euc(n)) :
    ‖mapOfVec v - mapOfVec w‖ ≤ ‖v - w‖ := by
  have h : mapOfVec v - mapOfVec w = mapOfVec (v - w) := by
    unfold mapOfVec
    simp only [← map_sub, matOfVec_sub]
  rw [h, norm_map_vec_eq_norm_vec]

private lemma norm_mapOfCovec_sub_le {n : ℕ} (v w : Euc(n)) :
    ‖mapOfCovec v - mapOfCovec w‖ ≤ ‖v - w‖ := by
  have h : mapOfCovec v - mapOfCovec w = mapOfCovec (v - w) := by
    unfold mapOfCovec
    simp only [← map_sub, matOfCovec_sub]
  rw [h, norm_map_covec_eq_norm_vec]

private lemma mapOfVec_apply {n : ℕ} (v x : Euc(n)) : (mapOfVec v x) 0 = ⟪v, x⟫ := by
  unfold mapOfVec
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (Matrix.toEuclideanLin (matOfVec v) x).ofLp 0 = _
  rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
  simp only [matOfVec, Matrix.mulVec, dotProduct]
  congr 1
  funext j
  ring

/- [SY25 Lemma 46] -/
theorem ek_spanning_imp_e_spanning (P : Local.Triangle) (P' : RationalApprox.Triangle)
    (hk : κApproxTri P P') (hP : ∀ i, ‖P i‖ ≤ 1) {θ φ ε : ℝ}
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
      mapOfVec (P (i + 1)),
      mapOfVec (P' (i + 1)),
      (rotM_mat θ φ)ᵀ.toEuclideanLin.toContinuousLinearMap,
      (rotMℚ_mat θ φ)ᵀ.toEuclideanLin.toContinuousLinearMap,
      rotR (π / 2), rotR (π / 2),
      rotM θ φ,
      rotMℚ θ φ,
      mapOfCovec (P i),
      mapOfCovec (P' i)
    ⟧

    have bound_P (i : Fin 3) : ‖P i‖ ≤ 1 + κ := calc
      ‖P i‖ ≤ 1 := hP i
      _ ≤ 1 + κ := by norm_num [κ]
    have bound_P' (i : Fin 3) : ‖(P' i : ℝ³)‖ ≤ 1 + κ :=
      calc ‖(P' i : ℝ³)‖ ≤ ‖P i‖ + ‖P i - (P' i : ℝ³)‖ := norm_le_insert (P i) (P' i : ℝ³)
        _ ≤ 1 + κ := add_le_add (hP i) (hk i)
    have hmvs : mv.size = 5 := by simp [mv]
    have hanb : MatVec.allNormsBelow mv [1 + κ, 1 + κ, 1, 1 + κ, 1 + κ] := by
      simp only [MatVec.allNormsBelow, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, MatVec.allNormsBelow.go, true_and, and_self, mv, norm_transpose_euc_lin,
        norm_map_vec_eq_norm_vec, norm_map_covec_eq_norm_vec]
      exact ⟨⟨⟨⟨
        ⟨bound_P' (i + 1), bound_P (i + 1)⟩,
        ⟨Mℚ_norm_bounded hθ hφ, bound_rotM θ φ⟩⟩, bound_rotR (π / 2)⟩,
        ⟨Mℚ_norm_bounded hθ hφ, bound_rotM θ φ⟩⟩, ⟨bound_P' i, bound_P i⟩⟩
    have hva : ⟪(rotR (π / 2)) ((rotM θ φ) (P i)), (rotM θ φ) (P (i + 1))⟫ = mv.valB := by
      simp only [MatVec.valB, mv, MatVec.compB]
      sorry
    have hvb : ⟪(rotR (π / 2)) (rotMℚ θ φ (P' i)), rotMℚ θ φ (P' (i + 1))⟫ = mv.valA := by
      simp [MatVec.valA, mv, MatVec.compA]
      sorry
    have hdbb : mv.DiffBoundedBy κ := by
      simp [MatVec.DiffBoundedBy, mv]
      clear hvb hva hanb hmvs mv
      split_ands
      · -- ‖mapOfVec (P' (i+1)) - mapOfVec (P (i+1))‖ ≤ κ
        calc ‖mapOfVec (P' (i + 1) : ℝ³) - mapOfVec (P (i + 1))‖
          _ ≤ ‖(P' (i + 1) : ℝ³) - P (i + 1)‖ := norm_mapOfVec_sub_le _ _
          _ = ‖P (i + 1) - (P' (i + 1) : ℝ³)‖ := norm_sub_rev _ _
          _ ≤ κ := hk (i + 1)
      · -- ‖(rotMℚ_mat θ φ)ᵀ.toCLM - (rotM_mat θ φ)ᵀ.toCLM‖ ≤ κ
        have h : (rotMℚ_mat θ φ)ᵀ.toEuclideanLin.toContinuousLinearMap -
                 (rotM_mat θ φ)ᵀ.toEuclideanLin.toContinuousLinearMap =
                 (rotMℚ_mat θ φ - rotM_mat θ φ)ᵀ.toEuclideanLin.toContinuousLinearMap := by
          simp only [← map_sub, Matrix.transpose_sub]
        rw [h, norm_transpose_euc_lin]
        calc ‖(rotMℚ_mat θ φ - rotM_mat θ φ).toEuclideanLin.toContinuousLinearMap‖
          _ = ‖rotMℚ θ φ - rotM θ φ‖ := by simp only [rotMℚ, rotM, ← map_sub]
          _ = ‖rotM θ φ - rotMℚ θ φ‖ := norm_sub_rev _ _
          _ ≤ κ := M_difference_norm_bounded θ φ hθ hφ
      · -- ‖rotR (π/2) - rotR (π/2)‖ ≤ κ  i.e., 0 ≤ κ
        norm_num [κ]
      · -- ‖rotMℚ θ φ - rotM θ φ‖ ≤ κ
        rw [norm_sub_rev]
        exact M_difference_norm_bounded θ φ hθ hφ
      · -- ‖mapOfCovec (P' i) - mapOfCovec (P i)‖ ≤ κ
        calc ‖mapOfCovec (P' i : ℝ³) - mapOfCovec (P i)‖
          _ ≤ ‖(P' i : ℝ³) - P i‖ := norm_mapOfCovec_sub_le _ _
          _ = ‖P i - (P' i : ℝ³)‖ := norm_sub_rev _ _
          _ ≤ κ := hk i
    suffices h : |mv.valA - mv.valB| ≤ 6 * κ by
      rw [hva, hvb]; rw [abs_sub_comm]; exact h
    grw [norm_sub_le_bound1 mv κ (by norm_num [κ]) hdbb hanb]
    rw [hmvs]
    norm_num [κ]
