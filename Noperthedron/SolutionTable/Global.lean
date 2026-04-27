import Noperthedron.Checker.Agreement
import Noperthedron.Checker.KappaApprox
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.SolutionTable.Basic
import Noperthedron.Vertices.Exact

namespace Noperthedron.Solution

private lemma Interval.epsilon_eq_radius (iv : Interval) : iv.epsilon = iv.radius := by
  unfold Interval.epsilon PoseInterval.radius
  set f : Param → ℚ := fun p => (iv.max.getParam p - iv.min.getParam p) / 2 with hf
  have hmax : (Finset.image f Finset.univ).max'
      (by rw [Finset.image_nonempty]; exact Finset.univ_nonempty) =
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
  rw [hmax]
  have h_div : ∀ a b : ℚ, (a ⊔ b) / 2 = (a / 2) ⊔ (b / 2) := by
    intro a b
    show (a ⊔ b) * (2 : ℚ)⁻¹ = a * 2⁻¹ ⊔ b * 2⁻¹
    rw [max_mul_of_nonneg _ _ (by norm_num : (0:ℚ) ≤ 2⁻¹)]
  simp only [hf, Pose.getParam]
  rw [h_div, h_div, h_div, h_div]

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
  have hr_eq_eps : r = row.epsilon := (Interval.epsilon_eq_radius row.interval).symm
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
    exceeds := hr_eq_eps ▸ hrow.G_gt_maxH
  }
  specialize hrg pc
  rw [hpbar_eq] at hrg
  push Not at hrg
  refine hrg q ?_ hqr
  have hmem : q ∈ Metric.closedBall iv.center iv.radius :=
    mem_closed_ball_center_of_mem iv q hqi'
  have hradius_eq : iv.radius = (r : ℝ) := by
    show row.toRealInterval.radius = ((row.interval.radius : ℚ) : ℝ)
    rw [← Agreement.row_epsilon_cast_eq_radius]
    exact_mod_cast Interval.epsilon_eq_radius row.interval
  rw [hradius_eq] at hmem
  exact hmem
