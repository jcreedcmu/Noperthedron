import Noperthedron.Checker.KappaApprox
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.SolutionTable.Basic
import Noperthedron.Vertices.Exact

namespace Noperthedron.Solution

/-- The rational `row.epsilon` (cast to `ℝ`) equals `PoseInterval.radius`
    of the corresponding `PoseInterval`. -/
theorem row_epsilon_cast_eq_radius (row : Row) :
    ((row.epsilon : ℚ) : ℝ) = row.toRealInterval.radius := by
  show ((row.interval.radius : ℚ) : ℝ) = row.interval.toReal.radius
  unfold Interval.toReal PoseInterval.radius
  simp only [PoseInterval.min, PoseInterval.max, Interval.minPose, Interval.maxPose]
  push_cast
  rfl

/-- Shared tail of the global and local bridge theorems: a "no Rupert pose
in the closed ball around the center pose at radius `row.epsilon`" conclusion
(as produced by `rational_global` / `rational_local`) yields "no Rupert pose
in the row's interval". -/
theorem no_rupert_in_interval_of_ball (row : Row)
    (h : ¬ ∃ q ∈ Metric.closedBall row.interval.centerPose.toReal
        ((row.epsilon : ℚ) : ℝ), RupertPose q exactPoly.hull) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  rintro ⟨q, hqi, hqr⟩
  let iv := row.toRealInterval
  have hpbar_eq : row.interval.centerPose.toReal = iv.center := by
    show row.interval.centerPose.toReal = row.interval.toReal.center
    have hc (p : Param) : ((row.interval.center p : ℚ) : ℝ) =
        row.interval.toReal.center.getParam p :=
      (Interval.toReal_center_getParam row.interval p).symm
    refine Pose.mk.injEq .. |>.mpr ⟨hc .θ₁, hc .θ₂, hc .φ₁, hc .φ₂, hc .α⟩
  rw [hpbar_eq] at h
  push Not at h
  refine h q ?_ hqr
  have hqi' : q ∈ iv := hqi
  have hmem : q ∈ Metric.closedBall iv.center iv.radius :=
    mem_closed_ball_center_of_mem iv q hqi'
  rw [(row_epsilon_cast_eq_radius row).symm] at hmem
  exact hmem

theorem valid_global_imp_no_rupert (row : Row)
    (hrow : row.ValidGlobal) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  let pℚ := row.interval.centerPose
  let r := row.interval.radius
  have hr : 0 ≤ r := PoseInterval.radius_nonneg row.interval
  have pc : RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
             exactPoly pythonPolyQ KappaApprox.exact_κApprox_python pℚ r := {
    j := row.S_index
    p_in_4 := hrow.center_in_fourQ
    w := row.w
    w_unit := by
      have h_wd : (0 : ℝ) < (row.w_denominator : ℝ) := mod_cast hrow.w_denominator_pos
      have h_unit : ((row.wx_numerator : ℝ)) ^ 2 + ((row.wy_numerator : ℝ)) ^ 2 =
          ((row.w_denominator : ℝ)) ^ 2 := mod_cast hrow.w_unit
      rw [show (toR2 row.w) = WithLp.toLp 2 (fun i => (row.w i : ℝ)) from rfl,
          EuclideanSpace.norm_eq, ← Real.sqrt_one]
      congr 1
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      show ((row.w 0 : ℝ)) ^ 2 + ((row.w 1 : ℝ)) ^ 2 = 1
      simp only [Row.w, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      field_simp
      linarith
    exceeds := hrow.G_gt_maxH
  }
  exact no_rupert_in_interval_of_ball row
    (RationalApprox.GlobalTheorem.rational_global pℚ r hr
      exactPoly pythonPolyQ KappaApprox.exact_κApprox_python pc)
