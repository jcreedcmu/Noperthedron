import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.Global
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.BoundsKappa

open scoped RealInnerProductSpace

namespace RationalApprox.GlobalTheorem

/--
A measure of how far an inner-shadow vertex S can "stick out"
-/
noncomputable
def Gℚ (p : Pose) (ε : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.innerℚ S, w⟫ - (ε * (|⟪p.rotR'ℚ (p.rotM₁ℚ S), w⟫| + |⟪p.rotRℚ (p.rotM₁θℚ S), w⟫| + |⟪p.rotRℚ (p.rotM₁φℚ S), w⟫|)
  + 9 * ε^2 / 2 + 4 * κ * (1 + 3 * ε))

/--
A measure of how far an outer-shadow vertex P can "reach" along w.
-/
noncomputable
def Hℚ (p : Pose) (ε : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ℚ P, w⟫ + ε * (|⟪p.rotM₂θℚ P, w⟫| + |⟪p.rotM₂φℚ P, w⟫|) + 2 * ε^2 + 3 * κ * (1 + 2 * ε)

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
noncomputable
def maxHℚ (p : Pose) (poly : GoodPoly) (ε : ℝ) (w : ℝ²) : ℝ :=
  poly.vertices.image (Hℚ p ε w) |>.max' <| by
    simp only [Finset.image_nonempty]
    exact poly.nonempty

/--
A compact way of saying "the pose satisfies the rational global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyhedron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure RationalGlobalTheoremPrecondition (poly poly_ : GoodPoly)
    (happrox : κApproxPoly poly.vertices poly_.vertices) (p : Pose) (ε : ℝ) : Type where
  S : ℝ³
  S_in_poly : S ∈ poly_.vertices
  p_in_4 : fourInterval.contains p
  w : ℝ²
  w_unit : ‖w‖ = 1
  exceeds : Gℚ p ε S w > maxHℚ p poly_ ε w

private lemma abs_le_abs_add_of_norm_sub_le {a b C : ℝ} (h : ‖a - b‖ ≤ C) : |a| ≤ |b| + C := by
  linarith [abs_sub_abs_le_abs_sub a b, (Real.norm_eq_abs _).symm ▸ h]

private lemma Gℚ_le_G {pbar : Pose} {ε : ℝ} (hε : ε > 0)
    {S S_ : ℝ³} {w : ℝ²}
    (hS : ‖S‖ ≤ 1) (hS_approx : ‖S - S_‖ ≤ κ) (hw : ‖w‖ = 1)
    (hp : fourInterval.contains pbar) :
    Gℚ pbar ε S_ w ≤ GlobalTheorem.G pbar ε S w := by
  -- Unfold both G definitions
  unfold Gℚ GlobalTheorem.G
  -- Key bounds from BoundsKappa
  set θ₁ : Set.Icc (-4 : ℝ) 4 := ⟨pbar.θ₁, hp.θ₁Bound⟩
  set φ₁ : Set.Icc (-4 : ℝ) 4 := ⟨pbar.φ₁, hp.φ₁Bound⟩
  set α_ : Set.Icc (-4 : ℝ) 4 := ⟨pbar.α, hp.αBound⟩
  -- inner ≈ innerℚ with 4κ bound
  have h_inner : ‖⟪pbar.rotR (pbar.rotM₁ S), w⟫ - ⟪pbar.rotRℚ (pbar.rotM₁ℚ S_), w⟫‖ ≤ 4 * κ := by
    show ‖⟪rotR ↑α_ (rotM ↑θ₁ ↑φ₁ S), w⟫ - ⟪rotRℚ ↑α_ (rotMℚ ↑θ₁ ↑φ₁ S_), w⟫‖ ≤ 4 * κ
    exact bounds_kappa_RM hS hS_approx hw
  -- The inner is ⟪pbar.inner S, w⟫ = ⟪pbar.rotR (pbar.rotM₁ S), w⟫
  have h_inner_eq : ⟪(pbar.inner S : ℝ²), w⟫ = ⟪pbar.rotR (pbar.rotM₁ S), w⟫ := by
    simp [Pose.inner_eq_RM pbar]
  -- innerℚ = rotRℚ ∘ rotM₁ℚ
  have h_innerQ_eq : ⟪pbar.innerℚ S_, w⟫ = ⟪pbar.rotRℚ (pbar.rotM₁ℚ S_), w⟫ := by
    simp [Pose.innerℚ, ContinuousLinearMap.comp_apply]
  -- R'M bound
  have h_R'M : ‖⟪pbar.rotR' (pbar.rotM₁ S), w⟫ - ⟪pbar.rotR'ℚ (pbar.rotM₁ℚ S_), w⟫‖ ≤ 4 * κ := by
    show ‖⟪rotR' ↑α_ (rotM ↑θ₁ ↑φ₁ S), w⟫ - ⟪rotR'ℚ ↑α_ (rotMℚ ↑θ₁ ↑φ₁ S_), w⟫‖ ≤ 4 * κ
    exact bounds_kappa_R'M hS hS_approx hw
  -- RMθ bound
  have h_RMθ : ‖⟪pbar.rotR (pbar.rotM₁θ S), w⟫ - ⟪pbar.rotRℚ (pbar.rotM₁θℚ S_), w⟫‖ ≤ 4 * κ := by
    show ‖⟪rotR ↑α_ (rotMθ ↑θ₁ ↑φ₁ S), w⟫ - ⟪rotRℚ ↑α_ (rotMθℚ ↑θ₁ ↑φ₁ S_), w⟫‖ ≤ 4 * κ
    exact bounds_kappa_RMθ hS hS_approx hw
  -- RMφ bound
  have h_RMφ : ‖⟪pbar.rotR (pbar.rotM₁φ S), w⟫ - ⟪pbar.rotRℚ (pbar.rotM₁φℚ S_), w⟫‖ ≤ 4 * κ := by
    show ‖⟪rotR ↑α_ (rotMφ ↑θ₁ ↑φ₁ S), w⟫ - ⟪rotRℚ ↑α_ (rotMφℚ ↑θ₁ ↑φ₁ S_), w⟫‖ ≤ 4 * κ
    exact bounds_kappa_RMφ hS hS_approx hw
  -- Now combine: Gℚ ≤ G
  rw [h_inner_eq, h_innerQ_eq]
  -- inner bound: real ≥ rational - 4κ
  have hi_le : ⟪pbar.rotRℚ (pbar.rotM₁ℚ S_), w⟫ ≤ ⟪pbar.rotR (pbar.rotM₁ S), w⟫ + 4 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_inner; rw [abs_le] at this; linarith [this.1]
  -- |abs_real| ≤ |abs_rational| + 4κ for the three ε-coefficient terms
  have hR'_abs := abs_le_abs_add_of_norm_sub_le h_R'M
  have hRθ_abs := abs_le_abs_add_of_norm_sub_le h_RMθ
  have hRφ_abs := abs_le_abs_add_of_norm_sub_le h_RMφ
  nlinarith

private lemma H_le_Hℚ {pbar : Pose} {ε : ℝ} (hε : ε > 0)
    {P P_ : ℝ³} {w : ℝ²}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1)
    (hp : fourInterval.contains pbar) :
    GlobalTheorem.H pbar ε w P ≤ Hℚ pbar ε w P_ := by
  unfold GlobalTheorem.H Hℚ
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨pbar.θ₂, hp.θ₂Bound⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨pbar.φ₂, hp.φ₂Bound⟩
  -- M bound
  have h_M : ‖⟪pbar.rotM₂ P, w⟫ - ⟪pbar.rotM₂ℚ P_, w⟫‖ ≤ 3 * κ := by
    show ‖⟪rotM ↑θ₂ ↑φ₂ P, w⟫ - ⟪rotMℚ ↑θ₂ ↑φ₂ P_, w⟫‖ ≤ 3 * κ
    exact bounds_kappa_M hP hP_approx hw
  -- Mθ bound
  have h_Mθ : ‖⟪pbar.rotM₂θ P, w⟫ - ⟪pbar.rotM₂θℚ P_, w⟫‖ ≤ 3 * κ := by
    show ‖⟪rotMθ ↑θ₂ ↑φ₂ P, w⟫ - ⟪rotMθℚ ↑θ₂ ↑φ₂ P_, w⟫‖ ≤ 3 * κ
    exact bounds_kappa_Mθ hP hP_approx hw
  -- Mφ bound
  have h_Mφ : ‖⟪pbar.rotM₂φ P, w⟫ - ⟪pbar.rotM₂φℚ P_, w⟫‖ ≤ 3 * κ := by
    show ‖⟪rotMφ ↑θ₂ ↑φ₂ P, w⟫ - ⟪rotMφℚ ↑θ₂ ↑φ₂ P_, w⟫‖ ≤ 3 * κ
    exact bounds_kappa_Mφ hP hP_approx hw
  -- Combine: H ≤ Hℚ
  -- Extract scalar bounds from norm bounds
  have hm_le : ⟪pbar.rotM₂ P, w⟫ ≤ ⟪pbar.rotM₂ℚ P_, w⟫ + 3 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_M; rw [abs_le] at this; linarith [this.2]
  -- Absolute value bounds: |real| ≤ |rational| + 3κ
  have hθ_abs := abs_le_abs_add_of_norm_sub_le h_Mθ
  have hφ_abs := abs_le_abs_add_of_norm_sub_le h_Mφ
  nlinarith

/--
[SY25] Theorem 43
-/
theorem rational_global (pbar : Pose) (ε : ℝ) (hε : ε > 0)
    (poly poly_ : GoodPoly)
    (happrox : κApproxPoly poly.vertices poly_.vertices)
    (_poly_pointsym : PointSym poly.hull)
    (pc : RationalGlobalTheoremPrecondition poly poly_ happrox pbar ε) :
    ¬ ∃ p ∈ pbar.closed_ball ε, RupertPose p poly.hull := by
  -- Step 1: Map S from poly_ to poly
  let S_real := happrox.bijection.symm ⟨pc.S, pc.S_in_poly⟩
  have hS_in : (S_real : ℝ³) ∈ poly.vertices := S_real.property
  have hS_approx : ‖(S_real : ℝ³) - pc.S‖ ≤ κ := by
    simpa [S_real, Equiv.apply_symm_apply] using happrox.approx S_real
  have hS_norm : ‖(S_real : ℝ³)‖ ≤ 1 := poly.vertex_radius_le_one _ hS_in
  -- Step 2: Build GlobalTheoremPrecondition
  have h_G_le := Gℚ_le_G hε hS_norm hS_approx pc.w_unit pc.p_in_4
  -- Step 3: Show maxH_real ≤ maxHℚ
  have h_maxH_le : GlobalTheorem.maxH pbar poly ε pc.w ≤ maxHℚ pbar poly_ ε pc.w := by
    unfold GlobalTheorem.maxH maxHℚ
    apply Finset.max'_le
    intro _ hh_real
    rcases Finset.mem_image.mp hh_real with ⟨P, hP_mem, rfl⟩
    -- Map P to P_
    let P_ := happrox.bijection ⟨P, hP_mem⟩
    have hP_norm : ‖P‖ ≤ 1 := poly.vertex_radius_le_one P hP_mem
    have hP_approx : ‖P - (P_ : ℝ³)‖ ≤ κ := happrox.approx ⟨P, hP_mem⟩
    have hH_le := H_le_Hℚ hε hP_norm hP_approx pc.w_unit pc.p_in_4
    calc GlobalTheorem.H pbar ε pc.w P
      _ ≤ Hℚ pbar ε pc.w P_ := hH_le
      _ ≤ (poly_.vertices.image (Hℚ pbar ε pc.w)).max' _ := by
          apply Finset.le_max'
          exact Finset.mem_image_of_mem _ P_.property
  -- Step 4: Build the precondition and apply global_theorem
  exact GlobalTheorem.global_theorem pbar ε hε poly _poly_pointsym {
    S := S_real
    S_in_poly := hS_in
    w := pc.w
    w_unit := pc.w_unit
    exceeds := by linarith [pc.exceeds]
  }
