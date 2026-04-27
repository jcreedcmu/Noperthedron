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
