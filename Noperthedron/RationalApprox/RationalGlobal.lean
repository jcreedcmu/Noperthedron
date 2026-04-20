import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Set.Operations
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
def Gℚ (p : Pose ℝ) (ε : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.innerℚ S, w⟫ - (ε * (|⟪p.rotR'ℚ (p.rotM₁ℚ S), w⟫| + |⟪p.rotRℚ (p.rotM₁θℚ S), w⟫| + |⟪p.rotRℚ (p.rotM₁φℚ S), w⟫|)
  + 9 * ε^2 / 2 + 4 * κ * (1 + 3 * ε))

/--
A measure of how far an outer-shadow vertex P can "reach" along w.
-/
noncomputable
def Hℚ (p : Pose ℝ) (ε : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ℚ P, w⟫ + ε * (|⟪p.rotM₂θℚ P, w⟫| + |⟪p.rotM₂φℚ P, w⟫|) + 2 * ε^2 + 3 * κ * (1 + 2 * ε)

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
noncomputable
def maxHℚ {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℝ) (poly : Polyhedron ι ℝ³) (ε : ℝ) (w : ℝ²) : ℝ :=
  Finset.image (Hℚ p ε w ∘ poly.v) Finset.univ  |>.max' <| by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr ne

/--
A compact way of saying "the pose satisfies the rational global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyhedron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure RationalGlobalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι ℝ³)
    (happrox : κApproxPoly poly.vertices poly_) (p : Pose ℚ) (ε : ℝ) : Type where
  j : ι
  p_in_4 : p ∈ fourInterval ℚ
  w : ℝ²
  w_unit : ‖w‖ = 1
  exceeds : Gℚ p.toReal ε (poly_.v j) w > maxHℚ p.toReal poly_ ε w

private lemma abs_le_abs_add_of_norm_sub_le {a b C : ℝ} (h : ‖a - b‖ ≤ C) : |a| ≤ |b| + C := by
  linarith [abs_sub_abs_le_abs_sub a b, (Real.norm_eq_abs _).symm ▸ h]

private lemma Gℚ_le_G {pbar : Pose ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    {S S_ : ℝ³} {w : ℝ²}
    (hS : ‖S‖ ≤ 1) (hS_approx : ‖S - S_‖ ≤ κ) (hw : ‖w‖ = 1)
    (hp : (fourInterval ℝ).contains pbar) :
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

private lemma H_le_Hℚ {pbar : Pose ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    {P P_ : ℝ³} {w : ℝ²}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - P_‖ ≤ κ) (hw : ‖w‖ = 1)
    (hp : (fourInterval ℝ).contains pbar) :
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
theorem rational_global {ι : Type} [Fintype ι] [Nonempty ι]
    (p : Pose ℚ) (ε : ℝ) (hε : 0 ≤ ε)
    (poly : GoodPoly ι) (poly_ : Polyhedron ι ℝ³)
    (happrox : κApproxPoly poly.vertices poly_)
    (_poly_pointsym : PointSym poly.hull)
    (pc : RationalGlobalTheoremPrecondition poly poly_ happrox p ε) :
    ¬ ∃ q ∈ Metric.closedBall p.toReal ε, RupertPose q poly.hull := by
  set pbar := p.toReal
  have hp4 : (fourInterval ℝ).contains pbar := fourInterval_contains_toReal pc.p_in_4
  -- Step 1: Map S from poly_ to poly via the bijection
  let j := pc.j
  let i := happrox.bijection.symm j
  let S_real := poly.vertices.v i
  have hS_in : S_real ∈ Set.range poly.vertices.v := ⟨i, rfl⟩
  have hS_approx : ‖S_real - poly_.v j‖ ≤ κ := by
    show ‖poly.vertices.v (happrox.bijection.symm j) - poly_.v j‖ ≤ κ
    have := happrox.approx (happrox.bijection.symm j)
    rwa [Equiv.apply_symm_apply] at this
  have hS_norm : ‖S_real‖ ≤ 1 := poly.vertex_radius_le_one i
  -- Step 2: Show maxH_real ≤ maxHℚ
  have h_maxH_le : GlobalTheorem.maxH pbar poly ε pc.w ≤ maxHℚ pbar poly_ ε pc.w := by
    unfold GlobalTheorem.maxH maxHℚ
    apply Finset.max'_le
    simp only [Function.comp, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨k, rfl⟩
    -- Map vertex k to approximate vertex
    let k' := happrox.bijection k
    have hk_norm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
    have hk_approx : ‖poly.vertices.v k - poly_.v k'‖ ≤ κ := happrox.approx k
    calc GlobalTheorem.H pbar ε pc.w (poly.vertices.v k)
      _ ≤ Hℚ pbar ε pc.w (poly_.v k') :=
          H_le_Hℚ hε hk_norm hk_approx pc.w_unit hp4
      _ ≤ _ := by
          show (Hℚ pbar ε pc.w ∘ poly_.v) k' ≤ _
          exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ k'))
  -- Step 3: Build the precondition and apply global_theorem
  exact GlobalTheorem.global_theorem pbar ε hε poly _poly_pointsym {
    S := S_real
    S_in_poly := hS_in
    w := pc.w
    w_unit := pc.w_unit
    exceeds := by linarith [pc.exceeds, Gℚ_le_G hε hS_norm hS_approx pc.w_unit hp4]
  }
