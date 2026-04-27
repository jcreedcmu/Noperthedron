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
