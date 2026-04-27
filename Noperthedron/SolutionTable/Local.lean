import Noperthedron.Checker.KappaApprox
import Noperthedron.SolutionTable.Basic
import Noperthedron.Local.Congruent
import Noperthedron.RationalApprox.RationalLocal
import Noperthedron.Vertices.Exact
import Noperthedron.Vertices.Symmetry

namespace Noperthedron.Solution

theorem valid_local_imp_no_rupert (tab : Table) (row : Row)
    (hrow : row.ValidLocal) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  let iv := row.toRealInterval
  let pbar := iv.center
  let r := iv.radius
  rintro ⟨q, hqi, hqr⟩
  have center_eq : ∀ p : Param, ((row.interval.center p : ℚ) : ℝ) =
      ((row.interval.min.getParam p : ℝ) + (row.interval.max.getParam p : ℝ)) / 2 := by
    intro p
    simp [Interval.center]
  have hθ₁ : (row.θ₁ : ℝ) = pbar.θ₁ := by
    rw [show (row.θ₁ : ℝ) = ((row.interval.center .θ₁ : ℚ) : ℝ) from rfl, center_eq]
    rfl
  have hφ₁ : (row.φ₁ : ℝ) = pbar.φ₁ := by
    rw [show (row.φ₁ : ℝ) = ((row.interval.center .φ₁ : ℚ) : ℝ) from rfl, center_eq]
    rfl
  have hθ₂ : (row.θ₂ : ℝ) = pbar.θ₂ := by
    rw [show (row.θ₂ : ℝ) = ((row.interval.center .θ₂ : ℚ) : ℝ) from rfl, center_eq]
    rfl
  have hφ₂ : (row.φ₂ : ℝ) = pbar.φ₂ := by
    rw [show (row.φ₂ : ℝ) = ((row.interval.center .φ₂ : ℚ) : ℝ) from rfl, center_eq]
    rfl
  have hα : (row.α : ℝ) = pbar.α := by
    rw [show (row.α : ℝ) = ((row.interval.center .α : ℚ) : ℝ) from rfl, center_eq]
    rfl
  obtain ⟨s, hs₁, hs₂⟩ := hrow.exists_symmetry
  have := RationalApprox.LocalTheorem.rational_local
           exactPoly pythonPolyQ KappaApprox.exact_κApprox_python
           row.Pi row.Qi
           (Noperthedron.TriangleSymmetry.congruent_of_apply s row.Pi row.Qi hs₁ hs₂)
           row.interval.centerPose hrow.center_in_fourQ
  sorry
