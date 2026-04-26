import Noperthedron.Checker.Agreement
import Noperthedron.Checker.KappaApprox
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.SolutionTable.Basic
import Noperthedron.Vertices.Exact

namespace Noperthedron.Solution

theorem valid_global_imp_no_rupert (_tab : Table) (row : Row)
    (hwf : row.WellFormed) (hrow : row.ValidGlobal) :
    ¬ ∃ q ∈ (row.interval : Set (Pose ℝ)), RupertPose q exactPolyhedron.hull := by
  let iv := row.toPoseInterval hwf
  let pbar := iv.center
  let r := iv.radius
  rintro ⟨q, hqi, hqr⟩
  have hqi : q ∈ iv := hqi
  have hqε : q ∈ Metric.closedBall pbar r := mem_closed_ball_center_of_mem iv q hqi
  have hr : 0 ≤ r := nonempty_closed_ball_radius_nonneg q pbar r hqε
  have hrg := RationalApprox.GlobalTheorem.rational_global
                 pbar r hr exactPoly pythonPoly
                 KappaApprox.exact_κApprox_python exactPoly_point_symmetric
  have center_eq : ∀ p : Param, ((row.interval.center p : ℚ) : ℝ) =
      ((row.interval.min p : ℝ) / DENOM + (row.interval.max p : ℝ) / DENOM) / 2 := by
    intro p
    simp [Interval.center, DENOM, DENOMQ]
    ring
  have hθ₁ : (row.θ₁ : ℝ) = pbar.θ₁ := by
    rw [show (row.θ₁ : ℝ) = ((row.interval.center .θ₁ : ℚ) : ℝ) from rfl, center_eq]; rfl
  have hφ₁ : (row.φ₁ : ℝ) = pbar.φ₁ := by
    rw [show (row.φ₁ : ℝ) = ((row.interval.center .φ₁ : ℚ) : ℝ) from rfl, center_eq]; rfl
  have hθ₂ : (row.θ₂ : ℝ) = pbar.θ₂ := by
    rw [show (row.θ₂ : ℝ) = ((row.interval.center .θ₂ : ℚ) : ℝ) from rfl, center_eq]; rfl
  have hφ₂ : (row.φ₂ : ℝ) = pbar.φ₂ := by
    rw [show (row.φ₂ : ℝ) = ((row.interval.center .φ₂ : ℚ) : ℝ) from rfl, center_eq]; rfl
  have hα : (row.α : ℝ) = pbar.α := by
    rw [show (row.α : ℝ) = ((row.interval.center .α : ℚ) : ℝ) from rfl, center_eq]; rfl
  have pc : RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
             exactPoly pythonPoly KappaApprox.exact_κApprox_python pbar r := {
    j := row.S_index
    p_in_4 := by
      rw [PoseInterval.contains_iff_components]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        simp only [fourInterval]
      · rw [← hθ₁]; exact_mod_cast hrow.θ₁_lb
      · rw [← hθ₁]; exact_mod_cast hrow.θ₁_ub
      · rw [← hθ₂]; exact_mod_cast hrow.θ₂_lb
      · rw [← hθ₂]; exact_mod_cast hrow.θ₂_ub
      · rw [← hφ₁]; exact_mod_cast hrow.φ₁_lb
      · rw [← hφ₁]; exact_mod_cast hrow.φ₁_ub
      · rw [← hφ₂]; exact_mod_cast hrow.φ₂_lb
      · rw [← hφ₂]; exact_mod_cast hrow.φ₂_ub
      · rw [← hα]; exact_mod_cast hrow.α_lb
      · rw [← hα]; exact_mod_cast hrow.α_ub
    w := WithLp.toLp 2 (fun i : Fin 2 => ((row.w i : ℝ)))
    w_unit := by
      have h_wd : (0 : ℝ) < (row.w_denominator : ℝ) := by exact_mod_cast hrow.w_denominator_pos
      have h_unit : ((row.wx_numerator : ℝ)) ^ 2 + ((row.wy_numerator : ℝ)) ^ 2 =
          ((row.w_denominator : ℝ)) ^ 2 := by exact_mod_cast hrow.w_unit
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_one]
      congr 1
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      show ((row.w 0 : ℝ)) ^ 2 + ((row.w 1 : ℝ)) ^ 2 = 1
      simp only [Row.w, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      field_simp
      linarith
    exceeds := by
      have h_cast : ((computeGQ row.θ₁ row.φ₁ row.α row.epsilon row.S row.w : ℚ) : ℝ) >
                    ((computeMaxHQ row.θ₂ row.φ₂ row.epsilon row.w : ℚ) : ℝ) := by
        exact_mod_cast hrow.G_gt_maxH
      rw [Agreement.computeGQ_eq_Gℚ row.θ₁ row.φ₁ row.α row.epsilon row.S row.w
            pbar hθ₁ hφ₁ hα,
          Agreement.computeMaxHQ_eq_maxHℚ row.θ₂ row.φ₂ row.epsilon row.w
            pbar hθ₂ hφ₂] at h_cast
      rw [Agreement.row_epsilon_cast_eq_radius] at h_cast
      exact h_cast
  }
  specialize hrg pc
  push Not at hrg
  exact hrg q hqε hqr
