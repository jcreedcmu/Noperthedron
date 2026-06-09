import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
  ∃ σ ∈ ({0, 1} : Set ℕ), ∀ i : Fin 3, (-1)^σ * ⟪X, P i⟫ > √2 * ε

noncomputable
def Triangle.Bε.lhs (v₁ v₂ : Euc(3)) (p : Pose ℝ) (ε : ℝ) : ℝ :=
   (⟪p.rotM₂ v₁, p.rotM₂ (v₁ - v₂)⟫ - 2 * ε * ‖v₁ - v₂‖ * (√2 + ε))
   / ((‖p.rotM₂ v₁‖ + √2 * ε) * (‖p.rotM₂ (v₁ - v₂)‖ + 2 * √2 * ε))

/--
Condition B_ε from [SY25] Theorem 36
-/
def Triangle.Bε {ι : Type} (Q : Triangle) (Qi : Fin 3 → ι)
    (v : ι → Euc(3)) (p : Pose ℝ) (ε δ r : ℝ) : Prop :=
  ∀ i : Fin 3, ∀ k : ι, k ≠ Qi i →
    (δ + √5 * ε) / r < Triangle.Bε.lhs (Q i) (v k) p ε

/-- The condition on δ in the Local Theorem -/
def BoundDelta (δ : ℝ) (p : Pose ℝ) (P Q : Triangle) : Prop :=
  ∀ i : Fin 3, δ ≥ ‖p.rotR (p.rotM₁ (P i)) - p.rotM₂ (Q i)‖/2

/-- The condition on r in the Local Theorem -/
def BoundR (r ε : ℝ) (p : Pose ℝ) (Q : Triangle): Prop :=
  ∀ i : Fin 3, ‖p.rotM₂ (Q i)‖ > r + √2 * ε

/--
A compact way of saying "the pose `p_` satisfies the Local Theorem precondition
at width `ε`": indices `Pi`, `Qi` of a pair of congruent triangles among the
vertices of `poly`, together with bounds `δ` and `r`, witnessing that no pose
within `ε` of `p_` can be a Rupert pose.
-/
structure LocalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p_ : Pose ℝ) (ε : ℝ) : Type where
  Pi : Fin 3 → ι
  Qi : Fin 3 → ι
  cong_tri : Triangle.Congruent (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  δ : ℝ
  r : ℝ
  hr : 0 < r
  hr₁ : BoundR r ε p_ (poly.vertices.v ∘ Qi)
  hδ : BoundDelta δ p_ (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  ae₁ : Triangle.Aε p_.vecX₁ (poly.vertices.v ∘ Pi) ε
  ae₂ : Triangle.Aε p_.vecX₂ (poly.vertices.v ∘ Qi) ε
  span₁ : Triangle.Spanning (poly.vertices.v ∘ Pi) p_.θ₁ p_.φ₁ ε
  span₂ : Triangle.Spanning (poly.vertices.v ∘ Qi) p_.θ₂ p_.φ₂ ε
  be : Triangle.Bε (poly.vertices.v ∘ Qi) Qi poly.vertices.v p_ ε δ r

/--
  [SY25] Theorem 36
-/
theorem local_theorem {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p_ : Pose ℝ) (ε : ℝ)
    (pc : LocalTheoremPrecondition poly p_ ε)
    : ¬∃ p ∈ Metric.closedBall p_ ε, RupertPose p poly.hull := by
  obtain ⟨Pi, Qi, cong_tri, δ, r, hr, hr₁, hδ, ae₁, ae₂, span₁, span₂, be⟩ := pc
  have hε : 0 < ε := span₁.pos
  set P : Triangle := poly.vertices.v ∘ Pi
  set Q : Triangle := poly.vertices.v ∘ Qi
  rintro ⟨p, hΨ₁, hΨ₂⟩
  obtain ⟨L, hL⟩ := cong_tri
  obtain ⟨σP, hσP₁, hσP₂⟩ := ae₁
  obtain ⟨σQ, hσQ₁, hσQ₂⟩ := ae₂
  let Y := vecX p.θ₁ p.φ₁
  let K := (-1 : ℝ)^(σP + σQ) • L.toContinuousLinearMap
  let Z := K (vecX p.θ₂ p.φ₂)
  have hδnn : 0 ≤ δ := le_trans (by positivity) (hδ 0)
  have hY : ‖Y‖ = 1 := by simp [Y, Bounding.vecX_norm_one]
  have hZ : ‖Z‖ = 1 := by simp [Z, K, norm_smul, Bounding.vecX_norm_one]
  have hα : |p.α - p_.α| ≤ ε := mem_closed_ball_abs_sub_α hΨ₁
  have hθ₁ : |p.θ₁ - p_.θ₁| ≤ ε := mem_closed_ball_abs_sub_θ₁ hΨ₁
  have hφ₁ : |p.φ₁ - p_.φ₁| ≤ ε := mem_closed_ball_abs_sub_φ₁ hΨ₁
  have hθ₂ : |p.θ₂ - p_.θ₂| ≤ ε := mem_closed_ball_abs_sub_θ₂ hΨ₁
  have hφ₂ : |p.φ₂ - p_.φ₂| ≤ ε := mem_closed_ball_abs_sub_φ₂ hΨ₁
  let P_ : Triangle := fun i ↦ (-1: ℝ) ^ σP • (P i)
  let Q_ : Triangle := fun i ↦ (-1: ℝ) ^ σQ • (Q i)
  have hP_ (i) : ‖P_ i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg_one_pow, one_mul]
    exact poly.vertex_radius_le_one (Pi i)
  have hQ_ (i) : ‖Q_ i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg_one_pow, one_mul]
    exact poly.vertex_radius_le_one (Qi i)
  have hPQ_ (i) : P_ i = K (Q_ i) := by
    simp [P_, Q_, K]
    rw [smul_smul, hL]
    congr 1
    rw [← pow_add, show σQ + (σP + σQ) = σP + 2 * σQ by ring,
        pow_add, pow_mul]
    norm_num
  have h₁ : Y ∈ Spanp P_ ∧ Z ∈ Spanp P_ := by
    constructor
    · have h₄ (i) : 0 < ⟪vecX p.θ₁ p.φ₁, P_ i⟫ := by
        specialize hσP₂ i
        rw [←real_inner_smul_right] at hσP₂
        exact Bounding.XPgt0 (hP_ i) hε hθ₁ hφ₁ hσP₂
      refine vecX_spanning P_ hθ₁ hφ₁ ?_ hP_ h₄
      exact spanning_neg σP span₁
    · have h₅ (i) : 0 < ⟪vecX p.θ₂ p.φ₂, Q_ i⟫ := by
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
  suffices h₂ : ∀ i, ⟪Z, P_ i⟫ < ⟪Y, P_ i⟫ by
    have h₃ := langles (hY.trans hZ.symm) h₁.1 h₁.2
    simp only [real_inner_comm Y, real_inner_comm Z] at h₃
    obtain h₃ | h₃ | h₃ := h₃ <;> exact lt_iff_not_ge.mp (h₂ _) h₃
  intro i
  have hQ₁ : ‖Q i‖ ≤ 1 := poly.vertex_radius_le_one (Qi i)
  -- apply lemma 15
  have h₃ : r < ‖rotM p.θ₂ p.φ₂ (Q i)‖ := Bounding.norm_M_apply_gt hQ₁ hε hθ₂ hφ₂ (hr₁ i)
  let T : Euc(2) := midpoint ℝ (p_.rotR (p_.rotM₁ (P i))) (p_.rotM₂ (Q i))
  have hT : ‖T - p_.rotM₂ (Q i)‖ ≤ δ := by
    simp only [T, midpoint_sub_right, invOf_eq_inv]
    rw [norm_smul, Real.norm_eq_abs, show |(2:ℝ)⁻¹| = 2⁻¹ by norm_num]
    linarith [hδ i]
  -- apply lemma 30
  have hP₁ : ‖P i‖ ≤ 1 := poly.vertex_radius_le_one (Pi i)
  obtain ⟨hd₁, hd₂⟩ := inCirc hP₁ hQ₁ hε hθ₁ hφ₁ hθ₂ hφ₂ hα hT
  -- apply lemma 33
  have h₅' (k : ι) (hkQ : k ≠ Qi i) :
      (δ + √5 * ε) / r <
        ⟪(rotM p.θ₂ p.φ₂) (Q i), (rotM p.θ₂ p.φ₂) (Q i - poly.vertices.v k)⟫ /
        (‖(rotM p.θ₂ p.φ₂) (Q i)‖ * ‖(rotM p.θ₂ p.φ₂) (Q i - poly.vertices.v k)‖) := by
    have h₆ := be i k hkQ
    unfold Triangle.Bε.lhs Pose.rotM₂ at h₆
    have h₅ := coss (Q := poly.vertices.v k) hQ₁ (poly.vertex_radius_le_one k) hε hθ₂ hφ₂
      ((show (0:ℝ) < (δ + √5 * ε) / r by positivity).trans h₆)
    linarith only [h₅, h₆]
  -- apply lemma 32
  let pm : Finset Euc(2) :=
    Finset.image (rotM p.θ₂ p.φ₂) (Finset.image poly.vertices.v Finset.univ)
  have h₈ : LocallyMaximallyDistant (δ + √5 * ε) (rotM p.θ₂ p.φ₂ (Q i)) T pm := by
    refine inner_ge_implies_LMD (r := r) ?_ ?_ hr h₃ ?_
    · exact Finset.mem_image_of_mem _
        (Finset.mem_image.mpr ⟨Qi i, Finset.mem_univ _, rfl⟩)
    · rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hd₂
      rw [add_comm, norm_sub_rev]
      exact hd₂
    · intro Pᵢ hPᵢ hPᵢQ
      simp only [pm, Finset.mem_image, Finset.mem_univ, true_and] at hPᵢ
      obtain ⟨q, ⟨k, rfl⟩, rfl⟩ := hPᵢ
      have hkQ : k ≠ Qi i := fun h => hPᵢQ (by rw [h]; rfl)
      rw [← map_sub]
      linarith [h₅' k hkQ]
  -- Step 1: Show rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈ sect (interior of pm)
  have h_in_interior_outer : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈ interior (convexHull ℝ (↑pm : Set ℝ²)) := by
    have h_inner_in_closure : p.inner (P i) ∈ closure (innerShadow p poly.hull) := by
      rw [Pose.inner_shadow_eq_img_inner]
      refine subset_closure (Set.mem_image_of_mem _ (subset_convexHull ℝ _ ?_))
      exact ⟨Pi i, rfl⟩
    have h_outer_eq : outerShadow p poly.hull = convexHull ℝ (↑pm : Set ℝ²) := by
      rw [Pose.outer_shadow_eq_M]
      have hpoly_hull : poly.hull =
          convexHull ℝ (↑(Finset.image poly.vertices.v Finset.univ) : Set ℝ³) := by
        simp [GoodPoly.hull, Polyhedron.hull, Set.range]
      rw [hpoly_hull]
      have hpm : (↑pm : Set ℝ²) =
          p.rotM₂ '' ↑(Finset.image poly.vertices.v Finset.univ) := by
        simp only [pm, Finset.coe_image, Pose.rotM₂]
      rw [hpm]
      exact AffineMap.image_convexHull p.rotM₂.toAffineMap _
    have h_inner_eq : p.inner (P i) = rotR p.α (rotM p.θ₁ p.φ₁ (P i)) := by
      simp only [Pose.inner_eq_RM, Pose.rotR, Pose.rotM₁, Function.comp_apply]
    rw [← h_outer_eq, ← h_inner_eq]; exact hΨ₂ h_inner_in_closure
  -- Step 2: Combine with hd₁ to get sect membership, apply LMD for norm bound
  have h_sect : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈ sect (δ + √5 * ε) T pm :=
    ⟨by rw [add_comm]; exact hd₁, h_in_interior_outer⟩
  have h_norm_bound : ‖rotM p.θ₁ p.φ₁ (P i)‖ < ‖rotM p.θ₂ p.φ₂ (Q i)‖ := by
    rw [← Bounding.rotR_preserves_norm p.α]; exact h₈ _ h_sect
  -- Step 3: Apply pythagoras to convert norm bounds to inner product bounds
  have h_inner_sq : ⟪vecX p.θ₂ p.φ₂, Q i⟫^2 < ⟪Y, P i⟫^2 := by
    have h_norm_eq : ‖P i‖ = ‖Q i‖ := by rw [hL i, L.norm_map]
    rw [←sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)] at h_norm_bound
    -- pythagoras gives: ‖rotM θ φ P‖² = ‖P‖² - ⟪vecX θ φ, P⟫²
    -- So: ‖P‖² - ⟪Y, P i⟫² < ‖Q‖² - ⟪vecX θ₂ φ₂, Q i⟫² with ‖P‖ = ‖Q‖
    simp only [Local.pythagoras, h_norm_eq] at h_norm_bound
    linarith
  -- Step 4: Handle sign conventions using |(-1)^σ * x| = |x|
  have hYP_pos : 0 < ⟪Y, P_ i⟫ := by
    have h_eq : ⟪vecX p_.θ₁ p_.φ₁, P_ i⟫ = (-1 : ℝ)^σP * ⟪p_.vecX₁, P i⟫ := by simp only [P_, real_inner_smul_right, Pose.vecX₁]
    exact Bounding.XPgt0 (hP_ i) hε hθ₁ hφ₁ (by rw [h_eq]; exact hσP₂ i)
  -- ⟪Z, P_ i⟫ = (-1)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ and ⟪Y, P_ i⟫ = (-1)^σP * ⟪Y, P i⟫
  have h_ZP : ⟪Z, P_ i⟫ = (-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ := by
    simp only [Z, K, P_, ContinuousLinearMap.coe_smul', _root_.Pi.smul_apply,
      LinearIsometry.coe_toContinuousLinearMap, inner_smul_left, real_inner_smul_right, RCLike.conj_to_real]
    rw [hL i, L.inner_map_map]
    have h_exp : (-1 : ℝ)^(σP + σQ) * (-1 : ℝ)^σP = (-1 : ℝ)^σQ := by
      rw [← pow_add, show σP + σQ + σP = 2 * σP + σQ by ring,
          pow_add, pow_mul]; norm_num
    rw [←mul_assoc, h_exp]
  have h_YP : ⟪Y, P_ i⟫ = (-1 : ℝ)^σP * ⟪Y, P i⟫ := by simp only [P_, real_inner_smul_right]
  rw [h_ZP, h_YP]
  -- The right-hand side is positive, so compare via absolute values
  have hYP_sign : 0 < (-1 : ℝ)^σP * ⟪Y, P i⟫ := h_YP ▸ hYP_pos
  calc (-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫
      ≤ |(-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫| := le_abs_self _
    _ = |⟪vecX p.θ₂ p.φ₂, Q i⟫| := by rw [abs_mul, abs_neg_one_pow, one_mul]
    _ < |⟪Y, P i⟫| := sq_lt_sq.mp h_inner_sq
    _ = |(-1 : ℝ)^σP * ⟪Y, P i⟫| := by rw [abs_mul, abs_neg_one_pow, one_mul]
    _ = (-1 : ℝ)^σP * ⟪Y, P i⟫ := abs_of_pos hYP_sign
