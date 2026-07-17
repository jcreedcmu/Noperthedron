module

public import Noperthedron.Checker.KappaApprox
public import Noperthedron.RationalApprox.RationalGlobal
public import Noperthedron.SolutionTable.Basic
public import Noperthedron.Vertices.Exact

public section


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

/-- Membership in the row's real interval box gives per-axis nearness to the
center pose at the row's per-axis half-widths. -/
theorem near_center_of_mem_toReal (row : Row) {q : Pose ℝ}
    (hq : q ∈ row.interval.toReal) :
    Pose.near row.interval.centerPose.toReal
      (row.εα : ℝ) (row.εθ₁ : ℝ) (row.εφ₁ : ℝ) (row.εθ₂ : ℝ) (row.εφ₂ : ℝ) q := by
  rw [NonemptyInterval.mem_def] at hq
  obtain ⟨hlo, hhi⟩ := hq
  rw [Pose.le_iff] at hlo hhi
  obtain ⟨l1, l2, l3, l4, l5⟩ := hlo
  obtain ⟨u1, u2, u3, u4, u5⟩ := hhi
  simp only [Interval.toReal, Interval.minPose, Interval.maxPose, PoseInterval.mk,
    PoseInterval.min, PoseInterval.max, Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁,
    Pose.toReal_φ₂, Pose.toReal_α] at l1 l2 l3 l4 l5 u1 u2 u3 u4 u5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Interval.centerPose, Interval.center, Pose.getParam, Pose.toReal_θ₁,
      Pose.toReal_θ₂, Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α,
      Row.εθ₁, Row.εφ₁, Row.εθ₂, Row.εφ₂, Row.εα]
    rw [abs_sub_le_iff]
    push_cast
    constructor <;> linarith

theorem valid_global_imp_no_rupert (row : Row)
    (hrow : row.ValidGlobal) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  let pℚ := row.interval.centerPose
  have pc : RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
             exactPoly pythonPolyQ KappaApprox.exact_κApprox_python pℚ
             row.εα row.εθ₁ row.εφ₁ row.εθ₂ row.εφ₂ := {
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
  have h := RationalApprox.GlobalTheorem.rational_global pℚ
    row.εα row.εθ₁ row.εφ₁ row.εθ₂ row.εφ₂
    hrow.εα_pos.le hrow.εθ₁_pos.le hrow.εφ₁_pos.le hrow.εθ₂_pos.le hrow.εφ₂_pos.le
    exactPoly pythonPolyQ KappaApprox.exact_κApprox_python pc
  rintro ⟨q, hqi, hqr⟩
  exact h ⟨q, near_center_of_mem_toReal row hqi, hqr⟩

end Noperthedron.Solution
end
