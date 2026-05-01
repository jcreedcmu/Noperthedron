import Noperthedron.Checker.KappaApprox
import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Global
import Noperthedron.Local.Congruent
import Noperthedron.RationalApprox.RationalLocal
import Noperthedron.Vertices.Exact
import Noperthedron.Vertices.Symmetry

namespace Noperthedron.Solution

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- The transported triangle for `exact_κApprox_python` is just `pythonVertex ∘ Pi`. -/
private lemma transportTri_python (Pi : Fin 3 → VertexIndex) :
    (KappaApprox.exact_κApprox_python.transportTri Pi : Local.TriangleQ) =
      pythonVertex ∘ Pi := rfl

/-- Bridge from rational `P_spanning` to real `κSpanning` for the Python polyhedron. -/
private lemma py_κSpanning_of_rational
    (Pi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε : ℚ) (hε : 0 < ε)
    (h : ∀ i : Fin 3,
      2 * ε * (sqrt_twoℚ + ε) + 6 * κQ <
        (rot90 *ᵥ (RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ (pythonVertex (Pi i)))) ⬝ᵥ
          (RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ (pythonVertex (Pi (i + 1))))) :
    (KappaApprox.exact_κApprox_python.transportTri Pi).toReal.κSpanning
      (p.toReal.θ₁ : ℝ) (p.toReal.φ₁ : ℝ) ε := by
  refine ⟨by exact_mod_cast hε, fun i => ?_⟩
  -- bridge the rational LHS to the real κSpanning LHS
  have hreal : (((rot90 *ᵥ (RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ (pythonVertex (Pi i)))) ⬝ᵥ
        (RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ (pythonVertex (Pi (i + 1)))) : ℚ) : ℝ) =
      ⟪rotR (π / 2) (RationalApprox.rotMℚℝ (p.θ₁ : ℝ) (p.φ₁ : ℝ) (toR3 (pythonVertex (Pi i)))),
        RationalApprox.rotMℚℝ (p.θ₁ : ℝ) (p.φ₁ : ℝ) (toR3 (pythonVertex (Pi (i + 1))))⟫ := by
    exact RationalApprox.rot90_rotMℚ_inner_eq_real_inner _ _ _ _
  -- Cast rational hypothesis to ℝ
  have hi := h i
  have hcast : ((2 * ε * (sqrt_twoℚ + ε) + 6 * κQ : ℚ) : ℝ) <
      (((rot90 *ᵥ (RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ (pythonVertex (Pi i)))) ⬝ᵥ
        (RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ (pythonVertex (Pi (i + 1)))) : ℚ) : ℝ) := by
    exact_mod_cast hi
  rw [hreal] at hcast
  -- bound 2 * ε * (sqrt_twoℚ + ε) ≥ 2 * ε * (√2 + ε), and 6 * κQ ≥ 6 * κ (equal in fact)
  have hε_real : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε.le
  have hsqrt2 : (√2 : ℝ) ≤ (142 / 100 : ℝ) := by
    have h : Real.sqrt 2 < (1.42 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  have hcastκ : ((κQ : ℚ) : ℝ) = RationalApprox.κ := by
    show ((1 / 10 ^ 10 : ℚ) : ℝ) = 1 / 10 ^ 10
    push_cast; rfl
  have hbound :
      2 * (ε : ℝ) * (Real.sqrt 2 + ε) + 6 * RationalApprox.κ ≤
        ((2 * ε * (sqrt_twoℚ + ε) + 6 * κQ : ℚ) : ℝ) := by
    push_cast [hcastκ]
    have hk : 2 * (ε : ℝ) * (Real.sqrt 2 + ε) ≤ 2 * (ε : ℝ) * (142 / 100 + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- Need to convert hcast goal `2 * ε * (√2 + ε) + 6 * κ < ⟪..⟫`
  exact lt_of_le_of_lt hbound hcast

/-- Bridge from rational `Q_spanning` to real `κSpanning`. -/
private lemma py_κSpanning_of_rational_Q
    (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε : ℚ) (hε : 0 < ε)
    (h : ∀ i : Fin 3,
      2 * ε * (sqrt_twoℚ + ε) + 6 * κQ <
        (rot90 *ᵥ (RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ (pythonVertex (Qi i)))) ⬝ᵥ
          (RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ (pythonVertex (Qi (i + 1))))) :
    (KappaApprox.exact_κApprox_python.transportTri Qi).toReal.κSpanning
      (p.toReal.θ₂ : ℝ) (p.toReal.φ₂ : ℝ) ε := by
  refine ⟨by exact_mod_cast hε, fun i => ?_⟩
  have hreal : (((rot90 *ᵥ (RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ (pythonVertex (Qi i)))) ⬝ᵥ
        (RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ (pythonVertex (Qi (i + 1)))) : ℚ) : ℝ) =
      ⟪rotR (π / 2) (RationalApprox.rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ) (toR3 (pythonVertex (Qi i)))),
        RationalApprox.rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ) (toR3 (pythonVertex (Qi (i + 1))))⟫ := by
    exact RationalApprox.rot90_rotMℚ_inner_eq_real_inner _ _ _ _
  have hi := h i
  have hcast : ((2 * ε * (sqrt_twoℚ + ε) + 6 * κQ : ℚ) : ℝ) <
      (((rot90 *ᵥ (RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ (pythonVertex (Qi i)))) ⬝ᵥ
        (RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ (pythonVertex (Qi (i + 1)))) : ℚ) : ℝ) := by
    exact_mod_cast hi
  rw [hreal] at hcast
  have hε_real : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε.le
  have hsqrt2 : (√2 : ℝ) ≤ (142 / 100 : ℝ) := by
    have h : Real.sqrt 2 < (1.42 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  have hcastκ : ((κQ : ℚ) : ℝ) = RationalApprox.κ := by
    show ((1 / 10 ^ 10 : ℚ) : ℝ) = 1 / 10 ^ 10
    push_cast; rfl
  have hbound :
      2 * (ε : ℝ) * (Real.sqrt 2 + ε) + 6 * RationalApprox.κ ≤
        ((2 * ε * (sqrt_twoℚ + ε) + 6 * κQ : ℚ) : ℝ) := by
    push_cast [hcastκ]
    have hk : 2 * (ε : ℝ) * (Real.sqrt 2 + ε) ≤ 2 * (ε : ℝ) * (142 / 100 + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  exact lt_of_le_of_lt hbound hcast

theorem valid_local_imp_no_rupert (_tab : Table) (row : Row)
    (hrow : row.ValidLocal) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  let ε := row.epsilon
  let iv := row.toRealInterval
  let pbar := iv.center
  rintro ⟨q, hqi, hqr⟩
  have center_eq : ∀ p : Param, ((row.interval.center p : ℚ) : ℝ) =
      ((row.interval.min.getParam p : ℝ) + (row.interval.max.getParam p : ℝ)) / 2 := by
    intro p
    simp [Interval.center]
  obtain ⟨s, hs₁, hs₂⟩ := hrow.exists_symmetry
  have hε : 0 < ε := hrow.epsilon_pos
  have hpbar_eq : row.interval.centerPose.toReal = pbar := by
    show row.interval.centerPose.toReal = row.interval.toReal.center
    have h (p : Param) : ((row.interval.center p : ℚ) : ℝ) =
        row.interval.toReal.center.getParam p :=
      (Interval.toReal_center_getParam row.interval p).symm
    refine Pose.mk.injEq .. |>.mpr ⟨h .θ₁, h .θ₂, h .φ₁, h .φ₂, h .α⟩
  have := RationalApprox.LocalTheorem.rational_local
           exactPoly pythonPolyQ KappaApprox.exact_κApprox_python
           row.Pi row.Qi
           (Noperthedron.TriangleSymmetry.congruent_of_apply s row.Pi row.Qi hs₁ hs₂)
           row.interval.centerPose hrow.center_in_fourQ
           ε row.δ row.r hε hrow.rpos RationalApprox.sqrtApprox hrow.r_valid
           ?hdelta
           ?hx1
           ?hx2
           ?hspan1
           ?hspan2
           hrow.Bεℚ
  case hdelta =>
    intro i
    -- row.δ is Finset.max' over BoundDeltaℚi, so row.δ ≥ BoundDeltaℚi at i.
    have hi_mem : RationalApprox.LocalTheorem.BoundDeltaℚi
        row.interval.centerPose (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi)
        RationalApprox.sqrtApprox i ∈
        Finset.image (RationalApprox.LocalTheorem.BoundDeltaℚi
          row.interval.centerPose (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi)
          RationalApprox.sqrtApprox) Finset.univ :=
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have hle := Finset.le_max' _ _ hi_mem
    show row.δ ≥ RationalApprox.LocalTheorem.BoundDeltaℚi row.interval.centerPose
      (KappaApprox.exact_κApprox_python.transportTri row.Pi)
      (KappaApprox.exact_κApprox_python.transportTri row.Qi) RationalApprox.sqrtApprox i
    rw [transportTri_python row.Pi, transportTri_python row.Qi]
    exact hle
  case hx1 =>
    refine ⟨0, by simp, ?_⟩
    exact hrow.X₁_inner_gt
  case hx2 =>
    refine ⟨row.sigma_Q.val, ?_, ?_⟩
    · have hmem := row.sigma_Q.property
      simp only [Finset.mem_Icc] at hmem
      obtain ⟨_, h2⟩ := hmem
      interval_cases row.sigma_Q.val <;> simp
    · exact hrow.X₂_inner_gt
  case hspan1 =>
    exact py_κSpanning_of_rational row.Pi row.interval.centerPose ε hε hrow.P_spanning
  case hspan2 =>
    exact py_κSpanning_of_rational_Q row.Qi row.interval.centerPose ε hε hrow.Q_spanning
  -- Final goal: derive False from `this : ¬ ∃ p ∈ Metric.closedBall pℚ.toReal ε, RupertPose p exactPoly.hull`
  rw [hpbar_eq] at this
  push Not at this
  refine this q ?_ hqr
  have hqi' : q ∈ iv := hqi
  have hmem : q ∈ Metric.closedBall iv.center iv.radius :=
    mem_closed_ball_center_of_mem iv q hqi'
  rw [(row_epsilon_cast_eq_radius row).symm] at hmem
  exact hmem
