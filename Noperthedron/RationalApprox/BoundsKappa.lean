import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.MatrixBounds

open scoped RealInnerProductSpace

namespace RationalApprox

/-!
## Helper lemma

The 3κ bound pattern: for any pair of continuous linear maps `A, Aℚ` where
`‖A - Aℚ‖ ≤ κ`, `‖Aℚ‖ ≤ 1 + κ`, and points `P, P_` with
`‖P‖ ≤ 1`, `‖P - P_‖ ≤ κ`, we get `|⟪A P, w⟫ - ⟪Aℚ P_, w⟫| ≤ 3κ`.
-/

private lemma inner_three_kappa {E F : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [NormedSpace ℝ E]
    {A Aℚ : E →L[ℝ] F} {P P_ : E} {w : F}
    (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hAdiff : ‖A - Aℚ‖ ≤ κ) (hP : ‖P‖ ≤ 1)
    (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖@inner ℝ F _ (A P) w - @inner ℝ F _ (Aℚ P_) w‖ ≤ 3 * κ := by
  rw [← inner_sub_left]
  calc ‖@inner ℝ F _ (A P - Aℚ P_) w‖
    _ ≤ ‖A P - Aℚ P_‖ * ‖w‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = ‖A P - Aℚ P_‖ := by rw [hw, mul_one]
    _ ≤ 3 * κ := (clm_approx_apply_sub hAdiff hAℚnorm hP approx).trans (by unfold κ; norm_num)

/-!
## 4κ bounds

For the composed maps R ∘ A, we decompose:
  R(A P) - Rℚ(Aℚ P_) = R(A P - Aℚ P_) + (R - Rℚ)(Aℚ P_)

This gives ≤ ‖R‖ * ‖A P - Aℚ P_‖ + ‖R - Rℚ‖ * ‖Aℚ P_‖
-/

private lemma inner_four_kappa {E F G : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A Aℚ : E →L[ℝ] F} {R Rℚ : F →L[ℝ] G} {P P_ : E} {w : G}
    (hRnorm : ‖R‖ ≤ 1)
    (hRdiff : ‖R - Rℚ‖ ≤ κ)
    (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hAdiff : ‖A - Aℚ‖ ≤ κ)
    (hP : ‖P‖ ≤ 1) (approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1) :
    ‖@inner ℝ G _ (R (A P)) w - @inner ℝ G _ (Rℚ (Aℚ P_)) w‖ ≤ 4 * κ := by
  rw [← inner_sub_left, show R (A P) - Rℚ (Aℚ P_) = R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_) from by
    simp [map_sub, ContinuousLinearMap.sub_apply]]
  have hAP_diff : ‖A P - Aℚ P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hAdiff hAℚnorm hP approx
  have hAℚP_ : ‖Aℚ P_‖ ≤ (1 + κ) * (1 + κ) := approx_image_norm_le hAℚnorm hP approx
  calc ‖@inner ℝ G _ (R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)) w‖
    _ ≤ ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖ * ‖w‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = ‖R (A P - Aℚ P_) + (R - Rℚ) (Aℚ P_)‖ := by rw [hw, mul_one]
    _ ≤ ‖R (A P - Aℚ P_)‖ + ‖(R - Rℚ) (Aℚ P_)‖ := norm_add_le _ _
    _ ≤ ‖R‖ * ‖A P - Aℚ P_‖ + ‖R - Rℚ‖ * ‖Aℚ P_‖ := by
        gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (2 * κ + κ ^ 2) + κ * ((1 + κ) * (1 + κ)) := by
        have : (0 : ℝ) ≤ κ := by unfold κ; norm_num
        gcongr
    _ ≤ 4 * κ := by unfold κ; norm_num

section rational

variable {P : ℝ³} {P_ : Fin 3 → ℚ} {α θ φ : Set.Icc (-4 : ℚ) 4} {w : Fin 2 → ℚ}

/-! ## Cast helpers

Bridges between the rational `Fin n → ℚ` world and the real `WithLp.toLp 2 ∘ castℝ`
world used by the inner-product machinery.
-/

private lemma castℝ_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) :
    (fun i => ((M.mulVec v) i : ℝ)) = (M.map (fun x => (x : ℝ))).mulVec (fun i => (v i : ℝ)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast; rfl

private lemma castℝ_dotProduct {n : ℕ} (v w : Fin n → ℚ) :
    ((v ⬝ᵥ w : ℚ) : ℝ) = (fun i => (v i : ℝ)) ⬝ᵥ (fun i => (w i : ℝ)) := by
  simp [dotProduct]

private lemma rotMℚ_mat_castℝ (θ φ : ℚ) :
    (rotMℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMℚ_mat, sinℚ_match, cosℚ_match]

private lemma rotMθℚ_mat_castℝ (θ φ : ℚ) :
    (rotMθℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMθℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMθℚ_mat, sinℚ_match, cosℚ_match]

private lemma rotMφℚ_mat_castℝ (θ φ : ℚ) :
    (rotMφℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMφℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMφℚ_mat, sinℚ_match, cosℚ_match]

private lemma rotRℚ_mat_castℝ (α : ℚ) :
    (rotRℚ_mat (α : ℝ)) = (rotRℚ_mat α).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotRℚ_mat, sinℚ_match, cosℚ_match]

private lemma rotR'ℚ_mat_castℝ (α : ℚ) :
    (rotR'ℚ_mat (α : ℝ)) = (rotR'ℚ_mat α).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotR'ℚ_mat, sinℚ_match, cosℚ_match]

/-- One-matrix inner-product bridge: `⟪M_real (toR3 v), toR2 w⟫ = ((Mℚ.mulVec v ⬝ᵥ w : ℚ) : ℝ)`. -/
private lemma inner_one_bridge
    (Mℚ : Matrix (Fin 2) (Fin 3) ℚ) (M : Matrix (Fin 2) (Fin 3) ℝ)
    (hM : M = Mℚ.map (fun x => (x : ℝ)))
    (v : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ ℝ² _ (M.toEuclideanLin.toContinuousLinearMap (toR3 v)) (toR2 w) =
    ((Mℚ.mulVec v ⬝ᵥ w : ℚ) : ℝ) := by
  unfold toR3 toR2
  show @inner ℝ ℝ² _ (M.toEuclideanLin (WithLp.toLp 2 (fun i => (v i : ℝ))))
                     (WithLp.toLp 2 (fun i => (w i : ℝ))) = _
  rw [Matrix.toLpLin_apply]
  have h := EuclideanSpace.inner_eq_star_dotProduct
              (WithLp.toLp 2 (M.mulVec (fun i => (v i : ℝ))) : EuclideanSpace ℝ (Fin 2))
              (WithLp.toLp 2 (fun i => (w i : ℝ)))
  simp only [star_trivial] at h
  refine h.trans ?_
  rw [hM, ← castℝ_mulVec, ← castℝ_dotProduct, dotProduct_comm]

/-- Two-matrix inner-product bridge for the `R ∘ M`-style composition. -/
private lemma inner_two_bridge
    (Mℚ : Matrix (Fin 2) (Fin 2) ℚ) (Nℚ : Matrix (Fin 2) (Fin 3) ℚ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (N : Matrix (Fin 2) (Fin 3) ℝ)
    (hM : M = Mℚ.map (fun x => (x : ℝ))) (hN : N = Nℚ.map (fun x => (x : ℝ)))
    (v : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ ℝ² _ (M.toEuclideanLin.toContinuousLinearMap
                     (N.toEuclideanLin.toContinuousLinearMap (toR3 v))) (toR2 w) =
    ((Mℚ.mulVec (Nℚ.mulVec v) ⬝ᵥ w : ℚ) : ℝ) := by
  unfold toR3 toR2
  show @inner ℝ ℝ² _ (M.toEuclideanLin (N.toEuclideanLin (WithLp.toLp 2 (fun i => (v i : ℝ)))))
                     (WithLp.toLp 2 (fun i => (w i : ℝ))) = _
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply]
  have h := EuclideanSpace.inner_eq_star_dotProduct
              (WithLp.toLp 2 (M.mulVec (N.mulVec (fun i => (v i : ℝ))))
                : EuclideanSpace ℝ (Fin 2))
              (WithLp.toLp 2 (fun i => (w i : ℝ)))
  simp only [star_trivial] at h
  refine h.trans ?_
  rw [hM, hN, ← castℝ_mulVec, ← castℝ_mulVec, ← castℝ_dotProduct, dotProduct_comm]

/-- A `Set.Icc (-4 : ℚ) 4` element gives a `Set.Icc (-4 : ℝ) 4` membership after casting. -/
private lemma cast_Icc4_mem (a : Set.Icc (-4 : ℚ) 4) : (a : ℝ) ∈ Set.Icc (-4 : ℝ) 4 := by
  have h := a.property
  rw [Set.mem_Icc] at h
  rw [Set.mem_Icc]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-! ## Rational `bounds_kappa` lemmas ([SY25] Lemma 44)

Each lemma bounds the difference between a real inner product (using the exact
real rotations) and the cast of a rational dot product (using the rational
matrix-mulVec versions).
-/

lemma bounds_kappa_RMℚ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotM θ φ P), toR2 w⟫ - rotRℚ α (rotMℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    rw [show rotRℚℝ (α:ℝ) = (rotRℚ_mat (α:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotMℚℝ (θ:ℝ) (φ:ℝ) = (rotMℚ_mat (θ:ℝ) (φ:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotRℚ α (rotMℚ θ φ P_) =
            (rotRℚ_mat (α:ℚ)).mulVec ((rotMℚ_mat (θ:ℚ) (φ:ℚ)).mulVec P_) from by
          unfold rotRℚ rotMℚ; rw [Matrix.toLin'_apply, Matrix.toLin'_apply]]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (M_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_R'Mℚ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR' α (rotM θ φ P), toR2 w⟫ - rotR'ℚ α (rotMℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotR'ℚℝ (α:ℝ) (rotMℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotR'ℚ α (rotMℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    rw [show rotR'ℚℝ (α:ℝ) = (rotR'ℚ_mat (α:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotMℚℝ (θ:ℝ) (φ:ℝ) = (rotMℚ_mat (θ:ℝ) (φ:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotR'ℚ α (rotMℚ θ φ P_) =
            (rotR'ℚ_mat (α:ℚ)).mulVec ((rotMℚ_mat (θ:ℚ) (φ:ℚ)).mulVec P_) from by
          unfold rotR'ℚ rotMℚ; rw [Matrix.toLin'_apply, Matrix.toLin'_apply]]
    exact inner_two_bridge _ _ _ _ (rotR'ℚ_mat_castℝ α) (rotMℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR'_norm_one _))
    (R'_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (M_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_RMθℚ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotMθ θ φ P), toR2 w⟫ - rotRℚ α (rotMθℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMθℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMθℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    rw [show rotRℚℝ (α:ℝ) = (rotRℚ_mat (α:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotMθℚℝ (θ:ℝ) (φ:ℝ) = (rotMθℚ_mat (θ:ℝ) (φ:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotRℚ α (rotMθℚ θ φ P_) =
            (rotRℚ_mat (α:ℚ)).mulVec ((rotMθℚ_mat (θ:ℚ) (φ:ℚ)).mulVec P_) from by
          unfold rotRℚ rotMθℚ; rw [Matrix.toLin'_apply, Matrix.toLin'_apply]]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMθℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mθℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_RMφℚ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotR α (rotMφ θ φ P), toR2 w⟫ - rotRℚ α (rotMφℚ θ φ P_) ⬝ᵥ w‖ ≤ 4 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotRℚℝ (α:ℝ) (rotMφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_))) (toR2 w) =
      ((rotRℚ α (rotMφℚ θ φ P_) ⬝ᵥ w : ℚ) : ℝ) := by
    rw [show rotRℚℝ (α:ℝ) = (rotRℚ_mat (α:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotMφℚℝ (θ:ℝ) (φ:ℝ) = (rotMφℚ_mat (θ:ℝ) (φ:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotRℚ α (rotMφℚ θ φ P_) =
            (rotRℚ_mat (α:ℚ)).mulVec ((rotMφℚ_mat (θ:ℚ) (φ:ℚ)).mulVec P_) from by
          unfold rotRℚ rotMφℚ; rw [Matrix.toLin'_apply, Matrix.toLin'_apply]]
    exact inner_two_bridge _ _ _ _ (rotRℚ_mat_castℝ α) (rotMφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_four_kappa
    (le_of_eq (Bounding.rotR_norm_one _))
    (R_difference_norm_bounded _ (cast_Icc4_mem α))
    (Mφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mℚ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotM θ φ P, toR2 w⟫ - rotMℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    rw [show rotMℚℝ (θ:ℝ) (φ:ℝ) = (rotMℚ_mat (θ:ℝ) (φ:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotMℚ θ φ P_ = (rotMℚ_mat (θ:ℚ) (φ:ℚ)).mulVec P_ from by
          unfold rotMℚ; rw [Matrix.toLin'_apply]]
    exact inner_one_bridge _ _ (rotMℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (M_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mθℚ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotMθ θ φ P, toR2 w⟫ - rotMθℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMθℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMθℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    rw [show rotMθℚℝ (θ:ℝ) (φ:ℝ) = (rotMθℚ_mat (θ:ℝ) (φ:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotMθℚ θ φ P_ = (rotMθℚ_mat (θ:ℚ) (φ:ℚ)).mulVec P_ from by
          unfold rotMθℚ; rw [Matrix.toLin'_apply]]
    exact inner_one_bridge _ _ (rotMθℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mθℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mθ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

lemma bounds_kappa_Mφℚ
    (hP : ‖P‖ ≤ 1) (approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1) :
    ‖⟪rotMφ θ φ P, toR2 w⟫ - rotMφℚ θ φ P_ ⬝ᵥ w‖ ≤ 3 * κ := by
  have h_bridge :
      @inner ℝ ℝ² _ (rotMφℚℝ (θ:ℝ) (φ:ℝ) (toR3 P_)) (toR2 w) =
      ((rotMφℚ θ φ P_ ⬝ᵥ w : ℚ) : ℝ) := by
    rw [show rotMφℚℝ (θ:ℝ) (φ:ℝ) = (rotMφℚ_mat (θ:ℝ) (φ:ℝ)).toEuclideanLin.toContinuousLinearMap from rfl,
        show rotMφℚ θ φ P_ = (rotMφℚ_mat (θ:ℚ) (φ:ℚ)).mulVec P_ from by
          unfold rotMφℚ; rw [Matrix.toLin'_apply]]
    exact inner_one_bridge _ _ (rotMφℚ_mat_castℝ θ φ) _ _
  rw [← h_bridge]
  exact inner_three_kappa
    (Mφℚ_norm_bounded (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    (Mφ_difference_norm_bounded _ _ (cast_Icc4_mem θ) (cast_Icc4_mem φ))
    hP approx hw

end rational
