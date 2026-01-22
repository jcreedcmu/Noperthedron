import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm
import Noperthedron.PoseInterval
import Noperthedron.Local.Coss
import Noperthedron.Local.EpsSpanning
import Noperthedron.Local.LocallyMaximallyDistant
import Noperthedron.Local.Prelims
import Noperthedron.Local.OriginInTriangle
import Noperthedron.Local.Spanp

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 30 -/
theorem inCirc {δ ε θ₁ θ₁_ θ₂ θ₂_ φ₁ φ₁_ φ₂ φ₂_ α α_: ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε)
    (hθ₁ : |θ₁ - θ₁_| ≤ ε) (hφ₁ : |φ₁ - φ₁_| ≤ ε)
    (hθ₂ : |θ₂ - θ₂_| ≤ ε) (hφ₂ : |φ₂ - φ₂_| ≤ ε)
    (hα : |α - α_| ≤ ε) :
    let T : Euc(2) := midpoint ℝ (rotR α_ (rotM θ₁_ φ₁_ P)) (rotM θ₂_ φ₂_ Q)
    ‖T - rotM θ₂_ φ₂_ Q‖ ≤ δ →
    (rotR α (rotM θ₁ φ₁ P) ∈ Metric.ball T (√5 * ε + δ) ∧
     rotM θ₂ φ₂ Q ∈ Metric.ball T (√5 * ε + δ)) := by
  intro T hT
  simp only [mem_ball_iff_norm]
  constructor
  · grw [norm_sub_le_norm_sub_add_norm_sub _ (rotR α_ (rotM θ₁_ φ₁_ P)) _]
    have h₂ : rotR α_ (rotM θ₁_ φ₁_ P) - T = T - rotM θ₂_ φ₂_ Q := by simp [T]
    rw [h₂]
    grw [hT]
    rw [←ContinuousLinearMap.comp_apply, ←ContinuousLinearMap.comp_apply,
        ←ContinuousLinearMap.sub_apply]
    grw [ContinuousLinearMap.le_opNorm]
    gcongr 1
    grw [mul_le_of_le_one_right (norm_nonneg _) hP]
    exact Bounding.norm_RM_sub_RM_le hε hθ₁ hφ₁ hα
  · grw [norm_sub_le_norm_sub_add_norm_sub _ (rotM θ₂_ φ₂_ Q) _]
    rw [norm_sub_rev _ T]
    grw [hT]
    rw [←ContinuousLinearMap.sub_apply]
    grw [ContinuousLinearMap.le_opNorm]
    grw [mul_le_of_le_one_right (norm_nonneg _) hQ, Bounding.norm_M_sub_lt hε hθ₂ hφ₂]
    gcongr 2
    norm_num

/--
Condition A_ε from [SY25] Theorem 36
-/
def Triangle.Aε (X : ℝ³) (P : Triangle) (ε : ℝ) : Prop :=
  ∃ σ ∈ ({-1, 1} : Set ℤ), ∀ i : Fin 3, (-1)^σ * ⟪X, P i⟫ > √2 * ε

noncomputable
def Triangle.Bε.lhs (v₁ v₂ : Euc(3)) (p : Pose) (ε : ℝ) : ℝ :=
   (⟪p.rotM₂ v₁, p.rotM₂ (v₁ - v₂)⟫ - 2 * ε * ‖v₁ - v₂‖ * (√2 + ε))
   / ((‖p.rotM₂ v₁‖ + √2 * ε) * (‖p.rotM₂ (v₁ - v₂)‖ + 2 * √2 * ε))

/--
Condition B_ε from [SY25] Theorem 36
-/
def Triangle.Bε (Q : Triangle) (poly : Finset Euc(3)) (p : Pose) (ε δ r : ℝ) : Prop :=
  ∀ i : Fin 3, ∀ v ∈ poly, v ≠ Q i →
    (δ + √5 * ε) / r < Triangle.Bε.lhs (Q i) v p ε

--instance : Membership Triangle (Finset ℝ³) where
--  mem set tri := ∀ i : Fin 3, (tri i) ∈ set

/-- The condition on δ in the Local Theorem -/
def BoundDelta (δ : ℝ) (p : Pose) (P Q : Triangle) : Prop :=
  ∀ i : Fin 3, δ ≥ ‖p.rotR (p.rotM₁ (P i)) - p.rotM₂ (Q i)‖/2

/-- The condition on r in the Local Theorem -/
def BoundR (r ε : ℝ) (p : Pose) (Q : Triangle): Prop :=
  ∀ i : Fin 3, ‖p.rotM₂ (Q i)‖ > r + √2 * ε

--- XXX: this is a leftover shim that should be cleaned up
noncomputable
def shape_of (S : Finset ℝ³) : Shape where
  vertices := S

-- TODO: Somehow separate out the "local theorem precondition"
-- predicate in a way that is suitable for the computational step's
-- tree check.

/--
  [SY25] Theorem 36
-/
theorem local_theorem (P Q : Triangle)
    (cong_tri : P.Congruent Q)
    (poly : Finset ℝ³) (ne : poly.Nonempty)
    (hP : ∀ i, P i ∈ poly) (hQ : ∀ i, Q i ∈ poly)
    (radius_one : polyhedronRadius poly ne = 1)
    (p_ : Pose)
    (ε δ r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hr₁ : BoundR r ε p_ Q)
    (hδ : BoundDelta δ p_ P Q)
    (ae₁ : P.Aε p_.vecX₁ ε) (ae₂ : Q.Aε p_.vecX₂ ε)
    (span₁ : P.Spanning p_.θ₁ p_.φ₁ ε)
    (span₂ : Q.Spanning p_.θ₂ p_.φ₂ ε)
    (be : Q.Bε poly p_ ε δ r)
    : ¬∃ p ∈ p_.closed_ball ε, RupertPose p (shape_of poly |>.hull) := by
  rintro ⟨p, hΨ₁, hΨ₂⟩
  obtain ⟨L, hL⟩ := cong_tri
  obtain ⟨σP, hσP₁, hσP₂⟩ := ae₁
  obtain ⟨σQ, hσQ₁, hσQ₂⟩ := ae₂
  let Y := vecX p.θ₁ p.φ₁
  let K := (-1 : ℝ)^(σP + σQ) • L.toContinuousLinearMap
  let Z := K (vecX p.θ₂ p.φ₂)
  have hδnn : 0 ≤ δ := by
    specialize hδ 0; linarith only [hδ, norm_nonneg (p_.rotR (p_.rotM₁ (P 0)) - p_.rotM₂ (Q 0))]
  have hY : ‖Y‖ = 1 := by simp [Y, vecX_norm_one]
  have hZ : ‖Z‖ = 1 := by simp [Z, K, norm_smul, vecX_norm_one]
  let P_ : Triangle := fun i ↦ (-1: ℝ) ^ σP • (P i)
  let Q_ : Triangle := fun i ↦ (-1: ℝ) ^ σQ • (Q i)
  have hP_ (i) : ‖P_ i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    grw [polyhedron_vertex_norm_le_radius poly ne (hP i)]
    simp [radius_one, mul_one]
  have hQ_ (i) : ‖Q_ i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    grw [polyhedron_vertex_norm_le_radius poly ne (hQ i)]
    simp [radius_one, mul_one]
  have hPQ_ (i) : P_ i = K (Q_ i) := by
    simp [P_, Q_, K]
    rw [smul_smul, hL]
    congr 1
    rw [←zpow_add₀ (show (-1:ℝ) ≠ 0 by norm_num)]
    ring_nf
    rw [zpow_add₀ (show (-1:ℝ) ≠ 0 by norm_num), mul_comm σQ, zpow_mul]
    norm_num
  have h₁ : Y ∈ Spanp P_ ∧ Z ∈ Spanp P_ := by
    constructor
    · have hθ₁ : |p.θ₁ - p_.θ₁| ≤ ε := by
        have := closed_ball_imp_inner_params_near hΨ₁ 1
        simp [Pose.innerParams] at this
        rwa [abs_sub_comm]
      have hφ₁ : |p.φ₁ - p_.φ₁| ≤ ε := by
        have := closed_ball_imp_inner_params_near hΨ₁ 2
        simp [Pose.innerParams] at this
        rwa [abs_sub_comm]
      have h₄ (i) : 0 < ⟪vecX p.θ₁ p.φ₁, P_ i⟫ := by
        specialize hσP₂ i
        rw [←real_inner_smul_right] at hσP₂
        exact Bounding.XPgt0 (hP_ i) hε hθ₁ hφ₁ hσP₂
      refine vecX_spanning P_ hθ₁ hφ₁ ?_ hP_ h₄
      exact spanning_neg σP span₁
    · have hθ₂ : |p.θ₂ - p_.θ₂| ≤ ε := by
        have := closed_ball_imp_outer_params_near hΨ₁ 0
        simp [Pose.outerParams] at this
        rwa [abs_sub_comm]
      have hφ₂ : |p.φ₂ - p_.φ₂| ≤ ε := by
        have := closed_ball_imp_outer_params_near hΨ₁ 1
        simp [Pose.outerParams] at this
        rwa [abs_sub_comm]
      have h₅ (i) : 0 < ⟪vecX p.θ₂ p.φ₂, Q_ i⟫ := by
        specialize hσQ₂ i
        rw [←real_inner_smul_right] at hσQ₂
        exact Bounding.XPgt0 (hQ_ i) hε hθ₂ hφ₂ hσQ₂
      have h₆ : vecX p.θ₂ p.φ₂ ∈ Spanp Q_ := by
        refine vecX_spanning Q_ hθ₂ hφ₂ ?_ hQ_ h₅
        exact spanning_neg σQ span₂
      simp only [Spanp, Set.mem_setOf_eq, Z] at h₆ ⊢
      obtain ⟨c, hc₁, hc₂⟩ := h₆
      use c, hc₁
      simp [hc₂, map_sum, map_smul, ←hPQ_]
  have h₂ (i) : ⟪Z, P_ i⟫ < ⟪Y, P_ i⟫ := by
    rw [polyhedron_radius_iff] at radius_one
    have hQ₁ := radius_one.2 _ (hQ i)
    have hα : |p.α - p_.α| ≤ ε := by
      have := closed_ball_imp_inner_params_near hΨ₁ 0
      simp only [Fin.isValue, Pose.innerParams] at this
      rwa [abs_sub_comm]
    have hθ₁ : |p.θ₁ - p_.θ₁| ≤ ε := by
      have := closed_ball_imp_inner_params_near hΨ₁ 1
      simp only [Fin.isValue, Pose.innerParams] at this
      rwa [abs_sub_comm]
    have hφ₁ : |p.φ₁ - p_.φ₁| ≤ ε := by
      have := closed_ball_imp_inner_params_near hΨ₁ 2
      simp only [Fin.isValue, Pose.innerParams] at this
      rwa [abs_sub_comm]
    have hθ₂ : |p.θ₂ - p_.θ₂| ≤ ε := by
      have := closed_ball_imp_outer_params_near hΨ₁ 0
      simp only [Fin.isValue, Pose.outerParams, Matrix.cons_val_zero] at this
      rwa [abs_sub_comm]
    have hφ₂ : |p.φ₂ - p_.φ₂| ≤ ε := by
      have := closed_ball_imp_outer_params_near hΨ₁ 1
      simp only [Fin.isValue, Pose.outerParams] at this
      rwa [abs_sub_comm]
    -- apply lemma 15
    have h₃ : r < ‖rotM p.θ₂ p.φ₂ (Q i)‖ := Bounding.norm_M_apply_gt hQ₁ hε hθ₂ hφ₂ (hr₁ i)
    let T (i) : Euc(2) := midpoint ℝ (p_.rotR (p_.rotM₁ (P i))) (p_.rotM₂ (Q i))
    have hT : ‖T i - p_.rotM₂ (Q i)‖ ≤ δ := by
      simp only [T, midpoint_sub_right, invOf_eq_inv]
      rw [norm_smul, Real.norm_eq_abs, show |(2:ℝ)⁻¹| = 2⁻¹ by norm_num]
      specialize hδ i
      linarith
    -- apply lemma 30
    have hP₁ := radius_one.2 _ (hP i)
    obtain ⟨hd₁, hd₂⟩ := inCirc hP₁ hQ₁ hε hθ₁ hφ₁ hθ₂ hφ₂ hα hT
    -- apply lemma 33
    have h₅ (Qⱼ : Euc(3)) (hQⱼ₁ : Qⱼ ∈ poly) (hQⱼ₂ : Qⱼ ≠ Q i) :=
      coss (Q := Qⱼ) hQ₁ (radius_one.2 _ hQⱼ₁) hε hθ₂ hφ₂ ?pos
    case pos =>
      have h₆ := be i Qⱼ hQⱼ₁ hQⱼ₂
      unfold Triangle.Bε.lhs at h₆
      have h₇ : 0 < (δ + √5 * ε) / r := by positivity
      unfold Pose.rotM₂ at h₆
      exact h₇.trans h₆
    have h₅' (Qⱼ : Euc(3)) (hQⱼ₁ : Qⱼ ∈ poly) (hQⱼ₂ : Qⱼ ≠ Q i) :
        (δ + √5 * ε) / r <
          ⟪(rotM p.θ₂ p.φ₂) (Q i), (rotM p.θ₂ p.φ₂) (Q i - Qⱼ)⟫ /
          (‖(rotM p.θ₂ p.φ₂) (Q i)‖ * ‖(rotM p.θ₂ p.φ₂) (Q i - Qⱼ)‖) := by
      have h₆ := be i Qⱼ hQⱼ₁ hQⱼ₂
      unfold Triangle.Bε.lhs Pose.rotM₂ at h₆
      specialize h₅ Qⱼ hQⱼ₁ hQⱼ₂
      linarith only [h₅, h₆]
    -- apply lemma 32
    let pm : Finset Euc(2) := Finset.image (rotM p.θ₂ p.φ₂) poly
    have h₈ : LocallyMaximallyDistant (δ + √5 * ε) (rotM p.θ₂ p.φ₂ (Q i)) (T i) pm := by
      refine inner_ge_implies_LMD (r := r) ?_ ?_ hr h₃ ?_
      · simp only [Finset.mem_image, pm]
        exact ⟨Q i, hQ i, rfl⟩
      · simp only [T, Pose.rotR, Pose.rotM₁, Pose.rotM₂]
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hd₂
        rw [add_comm, norm_sub_rev]
        exact hd₂
      · intro Pᵢ hPᵢ hPᵢQ
        simp only [Finset.mem_image, pm] at hPᵢ
        obtain ⟨q, hq₁, hq₂⟩ := hPᵢ
        have hqQ : q ≠ Q i := by
          intro heq
          rw [heq] at hq₂
          exact hPᵢQ hq₂.symm
        have := h₅' q hq₁ hqQ
        rw [← hq₂, ← map_sub]
        linarith
    -- Step 1: Show rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈ sect (interior of pm)
    have h_in_interior_outer : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈ interior (convexHull ℝ (↑pm : Set ℝ²)) := by
      have h_inner_in_closure : p.inner (P i) ∈ closure (innerShadow p (shape_of poly).hull) := by
        rw [Pose.inner_shadow_eq_img_inner]
        exact subset_closure (Set.mem_image_of_mem _ (subset_convexHull ℝ _ (hP i)))
      have h_outer_eq : outerShadow p (shape_of poly).hull = convexHull ℝ (↑pm : Set ℝ²) := by
        rw [Pose.outer_shadow_eq_M]
        have hpm : (↑pm : Set ℝ²) = p.rotM₂ '' ↑poly := by simp only [pm, Finset.coe_image, Pose.rotM₂]
        rw [hpm]
        exact AffineMap.image_convexHull p.rotM₂.toAffineMap (↑poly)
      have h_inner_eq : p.inner (P i) = rotR p.α (rotM p.θ₁ p.φ₁ (P i)) := by
        simp only [Pose.inner_eq_RM, Pose.rotR, Pose.rotM₁, Function.comp_apply]
      rw [← h_outer_eq, ← h_inner_eq]; exact hΨ₂ h_inner_in_closure
    -- Step 2: Combine with hd₁ to get sect membership, apply LMD for norm bound
    have h_sect : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈ sect (δ + √5 * ε) (T i) pm :=
      ⟨by rw [add_comm]; exact hd₁, h_in_interior_outer⟩
    have h_norm_bound : ‖rotM p.θ₁ p.φ₁ (P i)‖ < ‖rotM p.θ₂ p.φ₂ (Q i)‖ := by
      rw [← Bounding.rotR_preserves_norm p.α]; exact h₈ _ h_sect
    -- Step 3: Apply pythagoras to convert norm bounds to inner product bounds
    have h_inner_sq : ⟪vecX p.θ₂ p.φ₂, Q i⟫^2 < ⟪Y, P i⟫^2 := by
      have h_pyth₁ := Local.pythagoras (θ := p.θ₁) (φ := p.φ₁) (P i)
      have h_pyth₂ := Local.pythagoras (θ := p.θ₂) (φ := p.φ₂) (Q i)
      have h_norm_eq : ‖P i‖ = ‖Q i‖ := by rw [hL i]; exact LinearIsometry.norm_map L (Q i)
      have h_sq_bound : ‖rotM p.θ₁ p.φ₁ (P i)‖^2 < ‖rotM p.θ₂ p.φ₂ (Q i)‖^2 := by
        have h1 : 0 ≤ ‖rotM p.θ₁ p.φ₁ (P i)‖ := norm_nonneg _
        have h2 : 0 ≤ ‖rotM p.θ₂ p.φ₂ (Q i)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖rotM p.θ₂ p.φ₂ (Q i)‖ - ‖rotM p.θ₁ p.φ₁ (P i)‖)]
      -- pythagoras gives: ‖rotM θ φ P‖² = ‖P‖² - ⟪vecX θ φ, P⟫²
      -- So: ‖P‖² - ⟪Y, P i⟫² < ‖Q‖² - ⟪vecX θ₂ φ₂, Q i⟫² with ‖P‖ = ‖Q‖
      nlinarith [sq_nonneg ⟪Y, P i⟫, sq_nonneg ⟪vecX p.θ₂ p.φ₂, Q i⟫]
    -- Step 4: Handle sign conventions using |(-1)^σ * x| = |x|
    have hYP_pos : 0 < ⟪Y, P_ i⟫ := by
      have h_eq : ⟪vecX p_.θ₁ p_.φ₁, P_ i⟫ = (-1 : ℝ)^σP * ⟪p_.vecX₁, P i⟫ := by simp only [P_, real_inner_smul_right, Pose.vecX₁]
      exact Bounding.XPgt0 (hP_ i) hε hθ₁ hφ₁ (by rw [h_eq]; exact hσP₂ i)
    have hZQ_pos : 0 < ⟪vecX p.θ₂ p.φ₂, Q_ i⟫ := by
      have h_eq : ⟪vecX p_.θ₂ p_.φ₂, Q_ i⟫ = (-1 : ℝ)^σQ * ⟪p_.vecX₂, Q i⟫ := by simp only [Q_, real_inner_smul_right, Pose.vecX₂]
      exact Bounding.XPgt0 (hQ_ i) hε hθ₂ hφ₂ (by rw [h_eq]; exact hσQ₂ i)
    -- ⟪Z, P_ i⟫ = (-1)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ and ⟪Y, P_ i⟫ = (-1)^σP * ⟪Y, P i⟫
    have h_ZP : ⟪Z, P_ i⟫ = (-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ := by
      simp only [Z, K, P_, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        LinearIsometry.coe_toContinuousLinearMap, inner_smul_left, real_inner_smul_right, RCLike.conj_to_real]
      rw [hL i, L.inner_map_map]
      have h_exp : (-1 : ℝ)^(σP + σQ) * (-1 : ℝ)^σP = (-1 : ℝ)^σQ := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), show σP + σQ + σP = 2 * σP + σQ by ring,
            zpow_add₀ (by norm_num), zpow_mul]; norm_num
      rw [←mul_assoc, h_exp]
    have h_YP : ⟪Y, P_ i⟫ = (-1 : ℝ)^σP * ⟪Y, P i⟫ := by simp only [P_, real_inner_smul_right]
    rw [h_ZP, h_YP]
    -- Both sides positive after sign, compare via absolute values
    have hZQ_sign : 0 < (-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ := by simp only [Q_, real_inner_smul_right] at hZQ_pos; exact hZQ_pos
    have hYP_sign : 0 < (-1 : ℝ)^σP * ⟪Y, P i⟫ := by rw [← h_YP]; exact hYP_pos
    calc (-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ = |(-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫| := (abs_of_pos hZQ_sign).symm
      _ = |⟪vecX p.θ₂ p.φ₂, Q i⟫| := by rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
      _ < |⟪Y, P i⟫| := by nlinarith [sq_abs ⟪vecX p.θ₂ p.φ₂, Q i⟫, sq_abs ⟪Y, P i⟫, abs_nonneg ⟪vecX p.θ₂ p.φ₂, Q i⟫, abs_nonneg ⟪Y, P i⟫]
      _ = |(-1 : ℝ)^σP * ⟪Y, P i⟫| := by rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
      _ = (-1 : ℝ)^σP * ⟪Y, P i⟫ := abs_of_pos hYP_sign
  have hYZ : ‖Y‖ = ‖Z‖ := by simp [hY, hZ]
  have h₃ := langles hYZ h₁.1 h₁.2
  simp only [real_inner_comm Y, real_inner_comm Z] at h₃
  obtain h₃ | h₃ | h₃ := h₃
  · specialize h₂ 0
    exact lt_iff_not_ge.mp h₂ h₃
  · specialize h₂ 1
    exact lt_iff_not_ge.mp h₂ h₃
  · specialize h₂ 2
    exact lt_iff_not_ge.mp h₂ h₃
