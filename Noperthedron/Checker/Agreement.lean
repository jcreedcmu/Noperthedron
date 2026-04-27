import Noperthedron.Checker.KappaApprox
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.SolutionTable.Basic

/-!
# Agreement between rational checker and real-valued theorem statements

Bridges the computable rational `computeGQ`/`computeMaxHQ` from
`Checker/Global.lean` to the noncomputable real-valued `Gℚ`/`maxHℚ`
from `RationalApprox/RationalGlobal.lean`.
-/

open RationalApprox RationalApprox.GlobalTheorem
open Noperthedron Noperthedron.Solution
open scoped RealInnerProductSpace

namespace Noperthedron.Solution.Agreement

/-! ## Coercion shorthand -/

/-- Coerce a `Fin n → ℚ` to a `Fin n → ℝ` pointwise. -/
abbrev castℝ {n : ℕ} (v : Fin n → ℚ) : Fin n → ℝ := fun i => (v i : ℝ)

/-! ## Matrix mulvec agreement: each rational `apply*` cast equals
    the corresponding `rotMℚ_mat` (etc.) acting on the cast vector. -/

lemma applyM_castℝ_eq (θ φ : ℚ) (S : Fin 3 → ℚ) :
    castℝ (applyM θ φ S) =
    (rotMℚ_mat (θ : ℝ) (φ : ℝ)).mulVec (castℝ S) := by
  funext i
  fin_cases i <;>
  · show ((applyM θ φ S _ : ℚ) : ℝ) = _
    simp only [applyM, rotMℚ_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    push_cast [Noperthedron.KappaApprox.sinQ_cast, Noperthedron.KappaApprox.cosQ_cast]
    simp; try ring

lemma applyMθ_castℝ_eq (θ φ : ℚ) (S : Fin 3 → ℚ) :
    castℝ (applyMθ θ φ S) =
    (rotMθℚ_mat (θ : ℝ) (φ : ℝ)).mulVec (castℝ S) := by
  funext i
  fin_cases i <;>
  · show ((applyMθ θ φ S _ : ℚ) : ℝ) = _
    simp only [applyMθ, rotMθℚ_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    push_cast [Noperthedron.KappaApprox.sinQ_cast, Noperthedron.KappaApprox.cosQ_cast]
    simp; try ring

lemma applyMφ_castℝ_eq (θ φ : ℚ) (S : Fin 3 → ℚ) :
    castℝ (applyMφ θ φ S) =
    (rotMφℚ_mat (θ : ℝ) (φ : ℝ)).mulVec (castℝ S) := by
  funext i
  fin_cases i <;>
  · show ((applyMφ θ φ S _ : ℚ) : ℝ) = _
    simp only [applyMφ, rotMφℚ_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    push_cast [Noperthedron.KappaApprox.sinQ_cast, Noperthedron.KappaApprox.cosQ_cast]
    simp; try ring

lemma applyR_castℝ_eq (α : ℚ) (u : Fin 2 → ℚ) :
    castℝ (applyR α u) =
    (rotRℚ_mat (α : ℝ)).mulVec (castℝ u) := by
  funext i
  fin_cases i <;>
  · show ((applyR α u _ : ℚ) : ℝ) = _
    simp only [applyR, rotRℚ_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    push_cast [Noperthedron.KappaApprox.sinQ_cast, Noperthedron.KappaApprox.cosQ_cast]
    simp; try ring

lemma applyR'_castℝ_eq (α : ℚ) (u : Fin 2 → ℚ) :
    castℝ (applyR' α u) =
    (rotR'ℚ_mat (α : ℝ)).mulVec (castℝ u) := by
  funext i
  fin_cases i <;>
  · show ((applyR' α u _ : ℚ) : ℝ) = _
    simp only [applyR', rotR'ℚ_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    push_cast [Noperthedron.KappaApprox.sinQ_cast, Noperthedron.KappaApprox.cosQ_cast]
    simp; try ring

/-! ## Inner-product / dot-product bridge -/

private lemma matrix_toCLM_toLp {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    M.toEuclideanLin.toContinuousLinearMap (WithLp.toLp 2 v) =
      WithLp.toLp 2 (M.mulVec v) := by
  show M.toEuclideanLin (WithLp.toLp 2 v) = _
  rw [Matrix.toLpLin_apply]

/-- Casting a rational dot product equals the dot product of casts. -/
lemma dotProduct_castℝ {n : ℕ} (v w : Fin n → ℚ) :
    ((v ⬝ᵥ w : ℚ) : ℝ) = (castℝ v) ⬝ᵥ (castℝ w) := by
  simp only [dotProduct, Rat.cast_sum, Rat.cast_mul]

/-- Generic inner-product bridge for two stacked matrix applications. -/
private lemma inner_two_matrix
    {m k n : ℕ}
    (M₁ : Matrix (Fin k) (Fin n) ℝ) (M₂ : Matrix (Fin m) (Fin k) ℝ)
    (v : Fin n → ℝ) (w : Fin m → ℝ) :
    @inner ℝ Euc(m) _
      (M₂.toEuclideanLin.toContinuousLinearMap
        (M₁.toEuclideanLin.toContinuousLinearMap (WithLp.toLp 2 v)))
      (WithLp.toLp 2 w) =
    w ⬝ᵥ M₂.mulVec (M₁.mulVec v) := by
  show inner ℝ (M₂.toEuclideanLin (M₁.toEuclideanLin (WithLp.toLp 2 v))) (WithLp.toLp 2 w) = _
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply]
  have h := EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (M₂.mulVec (M₁.mulVec v)) w
  simpa [star_trivial] using h

/-- Generic inner-product bridge for one matrix application. -/
private lemma inner_one_matrix
    {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    @inner ℝ Euc(m) _
      (M.toEuclideanLin.toContinuousLinearMap (WithLp.toLp 2 v))
      (WithLp.toLp 2 w) =
    w ⬝ᵥ M.mulVec v := by
  show inner ℝ (M.toEuclideanLin (WithLp.toLp 2 v)) (WithLp.toLp 2 w) = _
  rw [Matrix.toLpLin_apply]
  have h := EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (M.mulVec v) w
  simpa [star_trivial] using h

/-- Inner product of `(M₂ ∘ M₁) S` against `w` equals the rational dot
    product of `applyR α (applyM θ φ S)` against `w`. -/
private lemma inner_RM_eq (θ φ α : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ Euc(2) _
      ((rotRℚ_mat (α : ℝ)).toEuclideanLin.toContinuousLinearMap
        ((rotMℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
          (WithLp.toLp 2 (castℝ S))))
      (WithLp.toLp 2 (castℝ w)) =
    ((applyR α (applyM θ φ S) ⬝ᵥ w : ℚ) : ℝ) := by
  rw [inner_two_matrix, dotProduct_comm, dotProduct_castℝ,
      applyR_castℝ_eq, applyM_castℝ_eq]

private lemma inner_R'M_eq (θ φ α : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ Euc(2) _
      ((rotR'ℚ_mat (α : ℝ)).toEuclideanLin.toContinuousLinearMap
        ((rotMℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
          (WithLp.toLp 2 (castℝ S))))
      (WithLp.toLp 2 (castℝ w)) =
    ((applyR' α (applyM θ φ S) ⬝ᵥ w : ℚ) : ℝ) := by
  rw [inner_two_matrix, dotProduct_comm, dotProduct_castℝ,
      applyR'_castℝ_eq, applyM_castℝ_eq]

private lemma inner_RMθ_eq (θ φ α : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ Euc(2) _
      ((rotRℚ_mat (α : ℝ)).toEuclideanLin.toContinuousLinearMap
        ((rotMθℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
          (WithLp.toLp 2 (castℝ S))))
      (WithLp.toLp 2 (castℝ w)) =
    ((applyR α (applyMθ θ φ S) ⬝ᵥ w : ℚ) : ℝ) := by
  rw [inner_two_matrix, dotProduct_comm, dotProduct_castℝ,
      applyR_castℝ_eq, applyMθ_castℝ_eq]

private lemma inner_RMφ_eq (θ φ α : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ Euc(2) _
      ((rotRℚ_mat (α : ℝ)).toEuclideanLin.toContinuousLinearMap
        ((rotMφℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
          (WithLp.toLp 2 (castℝ S))))
      (WithLp.toLp 2 (castℝ w)) =
    ((applyR α (applyMφ θ φ S) ⬝ᵥ w : ℚ) : ℝ) := by
  rw [inner_two_matrix, dotProduct_comm, dotProduct_castℝ,
      applyR_castℝ_eq, applyMφ_castℝ_eq]

private lemma inner_M_eq (θ φ : ℚ) (P : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ Euc(2) _
      ((rotMℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
          (WithLp.toLp 2 (castℝ P)))
      (WithLp.toLp 2 (castℝ w)) =
    ((applyM θ φ P ⬝ᵥ w : ℚ) : ℝ) := by
  rw [inner_one_matrix, dotProduct_comm, dotProduct_castℝ, applyM_castℝ_eq]

private lemma inner_Mθ_eq (θ φ : ℚ) (P : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ Euc(2) _
      ((rotMθℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
          (WithLp.toLp 2 (castℝ P)))
      (WithLp.toLp 2 (castℝ w)) =
    ((applyMθ θ φ P ⬝ᵥ w : ℚ) : ℝ) := by
  rw [inner_one_matrix, dotProduct_comm, dotProduct_castℝ, applyMθ_castℝ_eq]

private lemma inner_Mφ_eq (θ φ : ℚ) (P : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ Euc(2) _
      ((rotMφℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
          (WithLp.toLp 2 (castℝ P)))
      (WithLp.toLp 2 (castℝ w)) =
    ((applyMφ θ φ P ⬝ᵥ w : ℚ) : ℝ) := by
  rw [inner_one_matrix, dotProduct_comm, dotProduct_castℝ, applyMφ_castℝ_eq]

/-! ## κQ ↔ κ -/

lemma κQ_cast : ((κQ : ℚ) : ℝ) = κ := by
  unfold κQ κ; push_cast; norm_num

/-! ## Bridge `row.epsilon` to `PoseInterval.radius` -/

/-- Max over all 5 `Param`s as an explicit 5-fold sup. -/
private lemma param_image_max'_eq {α : Type} [LinearOrder α] (f : Param → α)
    (h : (Finset.image f Finset.univ).Nonempty) :
    (Finset.image f Finset.univ).max' h =
      f .θ₁ ⊔ f .φ₁ ⊔ f .θ₂ ⊔ f .φ₂ ⊔ f .α := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨p, rfl⟩ := hy
    cases p <;> simp [le_sup_iff]
  · refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_ <;>
      · apply Finset.le_max'
        simp [Finset.mem_image]

/-- The rational `row.epsilon` (cast to `ℝ`) equals `PoseInterval.radius`
    of the corresponding `PoseInterval`. -/
theorem row_epsilon_cast_eq_radius (row : Row) :
    ((row.epsilon : ℚ) : ℝ) = row.toRealInterval.radius := by
  unfold Row.epsilon Interval.epsilon
  rw [Rat.cast_mono.map_finset_max']
  simp only [Finset.image_image]
  rw [param_image_max'_eq]
  simp only [Function.comp_apply]
  have h_div : ∀ a b : ℝ, (a ⊔ b) / 2 = (a / 2) ⊔ (b / 2) := by
    intro a b
    show (a ⊔ b) * (2 : ℝ)⁻¹ = a * 2⁻¹ ⊔ b * 2⁻¹
    rw [max_mul_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  unfold Row.toRealInterval Interval.toReal PoseInterval.radius
  simp only [PoseInterval.min, PoseInterval.max, Interval.minPose, Interval.maxPose]
  rw [h_div, h_div, h_div, h_div]
  have hcomp : ∀ p : Param,
      ((((row.interval.max.getParam p : ℚ) - (row.interval.min.getParam p : ℚ)) / 2 : ℚ) : ℝ) =
      ((row.interval.max.getParam p : ℝ) - (row.interval.min.getParam p : ℝ)) / 2 := by
    intro p
    push_cast
    ring
  rw [hcomp .θ₁, hcomp .φ₁, hcomp .θ₂, hcomp .φ₂, hcomp .α]
  simp [Pose.getParam, PoseInterval.min, PoseInterval.max]

end Noperthedron.Solution.Agreement
