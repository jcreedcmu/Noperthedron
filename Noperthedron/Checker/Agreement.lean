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

/-- The rational `row.epsilon` (cast to `ℝ`) equals `PoseInterval.radius`
    of the corresponding `PoseInterval`. -/
theorem row_epsilon_cast_eq_radius (row : Row) :
    ((row.epsilon : ℚ) : ℝ) = row.toRealInterval.radius := by
  show ((row.interval.radius : ℚ) : ℝ) = row.interval.toReal.radius
  unfold Interval.toReal PoseInterval.radius
  simp only [PoseInterval.min, PoseInterval.max, Interval.minPose, Interval.maxPose]
  push_cast
  rfl

end Noperthedron.Solution.Agreement
