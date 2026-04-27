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

theorem valid_global_imp_no_rupert (_tab : Table) (row : Row)
    (hrow : row.ValidGlobal) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  let pℚ := row.interval.centerPose
  let iv := row.toRealInterval
  let pbar := iv.center
  let r := row.interval.radius
  rintro ⟨q, hqi, hqr⟩
  have hqi' : q ∈ iv := hqi
  have hr : 0 ≤ r := PoseInterval.radius_nonneg row.interval
  have hpbar_eq : pℚ.toReal = pbar := by
    show row.interval.centerPose.toReal = row.interval.toReal.center
    have h (p : Param) : ((row.interval.center p : ℚ) : ℝ) =
        row.interval.toReal.center.getParam p :=
      (Interval.toReal_center_getParam row.interval p).symm
    refine Pose.mk.injEq .. |>.mpr ⟨h .θ₁, h .θ₂, h .φ₁, h .φ₂, h .α⟩
  have hrg := RationalApprox.GlobalTheorem.rational_global
                 pℚ r hr exactPoly pythonPolyQ
                 KappaApprox.exact_κApprox_python exactPoly_point_symmetric
  have pc : RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
             exactPoly pythonPolyQ KappaApprox.exact_κApprox_python pℚ r := {
    j := row.S_index
    p_in_4 := hrow.center_in_fourQ
    w := row.w
    w_unit := by
      have h_wd : (0 : ℝ) < (row.w_denominator : ℝ) := by exact_mod_cast hrow.w_denominator_pos
      have h_unit : ((row.wx_numerator : ℝ)) ^ 2 + ((row.wy_numerator : ℝ)) ^ 2 =
          ((row.w_denominator : ℝ)) ^ 2 := by exact_mod_cast hrow.w_unit
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
  specialize hrg pc
  rw [hpbar_eq] at hrg
  push Not at hrg
  refine hrg q ?_ hqr
  have hmem : q ∈ Metric.closedBall iv.center iv.radius :=
    mem_closed_ball_center_of_mem iv q hqi'
  rw [(row_epsilon_cast_eq_radius row).symm] at hmem
  exact hmem
