import Noperthedron.Local
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.EpsKapSpanning
import Noperthedron.RationalApprox.BoundsKappa3
import Noperthedron.RationalApprox.BoundsKappa4

open Local (Triangle)
open scoped RealInnerProductSpace Real

open RationalApprox (κ UpperSqrt)

namespace Local

def TriangleQ : Type := Fin 3 → Fin 3 → ℚ

def TriangleQ.toReal (t : TriangleQ) : Triangle :=
  fun i => toR3 (t i)

/--
Condition A_ε^ℚ from [SY25] Theorem 48
-/
def TriangleQ.Aεℚ (X : ℝ³) (P_ : TriangleQ) (ε : ℚ) : Prop :=
  ∃ σ ∈ ({-1, 1} : Set ℤ), ∀ i : Fin 3, (-1)^σ * ⟪X, P_.toReal i⟫ > √2 * ε + 3 * κ

noncomputable
def Triangle.Bεℚ.lhs (v₁ v₂ : Euc(3)) (p : Pose ℝ) (ε : ℚ) (su : UpperSqrt) : ℝ :=
   (⟪p.rotM₂ℚℝ v₁, p.rotM₂ℚℝ (v₁ - v₂)⟫ - 10 * κ - 2 * ε * (su.norm (v₁ - v₂) + 2 * κ) * (√2 + ε))
   / ((su.norm (p.rotM₂ℚℝ v₁) + √2 * ε + 3 * κ) * (su.norm (p.rotM₂ℚℝ (v₁ - v₂)) + 2 * √2 * ε + 6 * κ))

/--
Condition B_ε^ℚ from [SY25] Theorem 48
-/
def Triangle.Bεℚ {ι : Type} [Fintype ι] (Q_ : Triangle) (Qi : Fin 3 → ι)
    (v_ : ι → Euc(3)) (p : Pose ℝ) (ε δ : ℚ) (r : ℝ) (su : UpperSqrt) : Prop :=
  ∀ i : Fin 3, ∀ k : ι, k ≠ Qi i →
    (δ + √5 * ε) / r < Triangle.Bεℚ.lhs (Q_ i) (v_ k) p ε su

end Local

namespace RationalApprox

/--
If we have indices `Pi` for a triangle in `poly`, yield the corresponding
triangle in `poly_` which κ-approximates it.
-/
def κApproxPoly.transportTri {ι : Type} [Fintype ι]
    {A : Polyhedron ι ℝ³} {B : Polyhedron ι (Fin 3 → ℚ)}
    (Pi : Fin 3 → ι)
    (hpoly : κApproxPoly A B) : Local.TriangleQ :=
  fun i => B.v (hpoly.bijection (Pi i))

namespace LocalTheorem

/-- The condition on δ -/
def BoundDeltaℚ (δ : ℝ) (p : Pose ℝ) (P_ Q_ : Triangle) (su : UpperSqrt) : Prop :=
  ∀ i : Fin 3, δ ≥ su.norm (p.rotR (p.rotM₁ℚℝ (P_ i)) - p.rotM₂ℚℝ (Q_ i))/2 + 3 * κ

/-- The condition on r -/
def BoundRℚ (r ε : ℝ) (p : Pose ℝ) (Q_ : Triangle) (sl : LowerSqrt) : Prop :=
  ∀ i : Fin 3, sl.norm (p.rotM₂ℚℝ (Q_ i)) > r + √2 * ε + 3 * κ

/--
[SY25] Theorem 48 "The Rational Local Theorem"
-/
theorem rational_local {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (hpoly : κApproxPoly poly.vertices poly_)
    (Pi Qi : Fin 3 → ι)
    (cong_tri : Triangle.Congruent (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi))
    (p_ : Pose ℚ) (hp : p_ ∈ fourInterval ℚ)
    (ε δ : ℚ) (r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (su : UpperSqrt) (sl : LowerSqrt)
    (hr₁ : BoundRℚ r ε p_.toReal (hpoly.transportTri Qi).toReal sl)
    (hδ : BoundDeltaℚ δ p_.toReal (hpoly.transportTri Pi).toReal (hpoly.transportTri Qi).toReal su)
    (ae₁ : (hpoly.transportTri Pi).Aεℚ p_.toReal.vecX₁ℚℝ ε)
    (ae₂ : (hpoly.transportTri Qi).Aεℚ p_.toReal.vecX₂ℚℝ ε)
    (span₁ : (hpoly.transportTri Pi).toReal.κSpanning (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) ε)
    (span₂ : (hpoly.transportTri Qi).toReal.κSpanning (p_.θ₂ : ℝ) (p_.φ₂ : ℝ) ε)
    (be : (hpoly.transportTri Qi).toReal.Bεℚ Qi
          (fun k => poly_.toReal.v (hpoly.bijection k)) p_.toReal ε δ r su)
    : ¬∃ p ∈ Metric.closedBall p_.toReal ε, RupertPose p poly.hull := by
  have hεℝ : 0 < (ε : ℝ) := span₁.pos
  set p_ := p_.toReal
  have hp : (fourInterval ℝ).contains p_ := fourInterval_contains_toReal hp
  -- The rational `p_.θ₁` (cast to ℝ) is defeq to `p_.θ₁`, so the spanning hypotheses
  -- can be reinterpreted in terms of the real `p_`:
  change (hpoly.transportTri Pi).toReal.κSpanning p_.θ₁ p_.φ₁ ε at span₁
  change (hpoly.transportTri Qi).toReal.κSpanning p_.θ₂ p_.φ₂ ε at span₂
  -- Define the triangles from indices
  let P : Triangle := fun i => poly.vertices.v (Pi i)
  let Q : Triangle := fun i => poly.vertices.v (Qi i)
  -- Abbreviations for transported triangles
  set P_ := (hpoly.transportTri Pi).toReal
  set Q_ := (hpoly.transportTri Qi).toReal
  -- Angle subtypes
  set θ₁ : Set.Icc (-4 : ℝ) 4 := ⟨p_.θ₁, hp.θ₁Bound⟩
  set φ₁ : Set.Icc (-4 : ℝ) 4 := ⟨p_.φ₁, hp.φ₁Bound⟩
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨p_.θ₂, hp.θ₂Bound⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨p_.φ₂, hp.φ₂Bound⟩
  -- Vertex norm bounds
  have hPnorm (i : Fin 3) : ‖P i‖ ≤ 1 := poly.vertex_radius_le_one (Pi i)
  have hQnorm (i : Fin 3) : ‖Q i‖ ≤ 1 := poly.vertex_radius_le_one (Qi i)
  -- Approximation bounds
  have hPapprox (i : Fin 3) : ‖P i - P_ i‖ ≤ κ := hpoly.approx (Pi i)
  have hQapprox (i : Fin 3) : ‖Q i - Q_ i‖ ≤ κ := hpoly.approx (Qi i)
  -- Bridge: κSpanning → Spanning
  have span₁' : P.Spanning p_.θ₁ p_.φ₁ ε :=
    ek_spanning_imp_e_spanning P P_ (fun i => hPapprox i) hPnorm hp.θ₁Bound hp.φ₁Bound span₁
  have span₂' : Q.Spanning p_.θ₂ p_.φ₂ ε :=
    ek_spanning_imp_e_spanning Q Q_ (fun i => hQapprox i) hQnorm hp.θ₂Bound hp.φ₂Bound span₂
  -- Bridge: Aεℚ → Aε
  have ae₁' : P.Aε p_.vecX₁ ε := by
    obtain ⟨σ, hσ₁, hσ₂⟩ := ae₁
    refine ⟨σ, hσ₁, fun i => ?_⟩
    have hX : ‖⟪vecX ↑θ₁ ↑φ₁, P i⟫ - ⟪vecXℚℝ ↑θ₁ ↑φ₁, P_ i⟫‖ ≤ 3 * κ :=
      bounds_kappa3_X (θ := θ₁) (φ := φ₁) (hPnorm i) (hPapprox i)
    change (-1) ^ σ * ⟪vecX ↑θ₁ ↑φ₁, P i⟫ > √2 * ε
    have hσ₂i : (-1) ^ σ * ⟪vecXℚℝ ↑θ₁ ↑φ₁, P_ i⟫ > √2 * ε + 3 * κ := hσ₂ i
    rw [Real.norm_eq_abs] at hX
    have habs : |(-1 : ℝ) ^ σ| = 1 := abs_neg_one_zpow σ
    have hdiff : |(-1 : ℝ) ^ σ * (⟪vecX ↑θ₁ ↑φ₁, P i⟫ - ⟪vecXℚℝ ↑θ₁ ↑φ₁, P_ i⟫)| ≤ 3 * κ := by
      rw [abs_mul, habs, one_mul]; exact hX
    rw [abs_le] at hdiff
    linarith [hdiff.1, mul_sub ((-1 : ℝ) ^ σ) ⟪vecX ↑θ₁ ↑φ₁, P i⟫ ⟪vecXℚℝ ↑θ₁ ↑φ₁, P_ i⟫]
  have ae₂' : Q.Aε p_.vecX₂ ε := by
    obtain ⟨σ, hσ₁, hσ₂⟩ := ae₂
    refine ⟨σ, hσ₁, fun i => ?_⟩
    have hX : ‖⟪vecX ↑θ₂ ↑φ₂, Q i⟫ - ⟪vecXℚℝ ↑θ₂ ↑φ₂, Q_ i⟫‖ ≤ 3 * κ :=
      bounds_kappa3_X (θ := θ₂) (φ := φ₂) (hQnorm i) (hQapprox i)
    change (-1) ^ σ * ⟪vecX ↑θ₂ ↑φ₂, Q i⟫ > √2 * ε
    have hσ₂i : (-1) ^ σ * ⟪vecXℚℝ ↑θ₂ ↑φ₂, Q_ i⟫ > √2 * ε + 3 * κ := hσ₂ i
    rw [Real.norm_eq_abs] at hX
    have habs : |(-1 : ℝ) ^ σ| = 1 := abs_neg_one_zpow σ
    have hdiff : |(-1 : ℝ) ^ σ * (⟪vecX ↑θ₂ ↑φ₂, Q i⟫ - ⟪vecXℚℝ ↑θ₂ ↑φ₂, Q_ i⟫)| ≤ 3 * κ := by
      rw [abs_mul, habs, one_mul]; exact hX
    rw [abs_le] at hdiff
    linarith [hdiff.1, mul_sub ((-1 : ℝ) ^ σ) ⟪vecX ↑θ₂ ↑φ₂, Q i⟫ ⟪vecXℚℝ ↑θ₂ ↑φ₂, Q_ i⟫]
  -- Bridge: BoundRℚ → BoundR
  have hr₁' : Local.BoundR r ε p_ Q := by
    intro i
    have hsl : sl.norm ((rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) ≤ ‖(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := by
      show sl.f _ ≤ _; calc sl.f (‖(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ ^ 2)
        _ ≤ √(‖(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ ^ 2) := sl.bound _ (sq_nonneg _)
        _ = ‖(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := Real.sqrt_sq (norm_nonneg _)
    have hMQ : |(‖(rotM ↑θ₂ ↑φ₂) (Q i)‖ - ‖(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖)| ≤ 3 * κ :=
      bounds_kappa3_MQ (θ := θ₂) (φ := φ₂) (hQnorm i) (hQapprox i)
    show ‖(rotM ↑θ₂ ↑φ₂) (Q i)‖ > r + √2 * ε
    have hr₁i : sl.norm ((rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) > r + √2 * ε + 3 * κ := hr₁ i
    rw [abs_le] at hMQ
    linarith [hMQ.1]
  -- Bridge: BoundDeltaℚ → BoundDelta
  have hδ' : Local.BoundDelta δ p_ P Q := by
    intro i
    have := hδ i
    -- su.norm ≥ ‖·‖
    have hsu : ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ ≤
        su.norm (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)) := by
      exact UpperSqrt_norm_le su _
    -- ‖real - rational‖ ≤ 6κ
    have hM₁diff : ‖rotM (↑θ₁ : ℝ) ↑φ₁ - rotMℚℝ ↑θ₁ ↑φ₁‖ ≤ κ :=
      M_difference_norm_bounded _ _ θ₁.property φ₁.property
    have hM₁ℚnorm : ‖rotMℚℝ (↑θ₁ : ℝ) ↑φ₁‖ ≤ 1 + κ :=
      Mℚ_norm_bounded θ₁.property φ₁.property
    have hM₂diff : ‖rotM (↑θ₂ : ℝ) ↑φ₂ - rotMℚℝ ↑θ₂ ↑φ₂‖ ≤ κ :=
      M_difference_norm_bounded _ _ θ₂.property φ₂.property
    have hM₂ℚnorm : ‖rotMℚℝ (↑θ₂ : ℝ) ↑φ₂‖ ≤ 1 + κ :=
      Mℚ_norm_bounded θ₂.property φ₂.property
    have h₁ : ‖(rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)‖ ≤ 2 * κ + κ ^ 2 :=
      clm_approx_apply_sub hM₁diff hM₁ℚnorm (hPnorm i) (hPapprox i)
    have h₂ : ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ ≤ 2 * κ + κ ^ 2 :=
      clm_approx_apply_sub hM₂diff hM₂ℚnorm (hQnorm i) (hQapprox i)
    have hdiff : ‖(p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)) -
        (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i))‖ ≤ 4 * κ + 2 * κ ^ 2 := by
      show ‖(rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i)) - (rotM ↑θ₂ ↑φ₂) (Q i)) -
            (rotR p_.α ((rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i))‖ ≤ _
      have hrw : rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i)) - (rotM ↑θ₂ ↑φ₂) (Q i) -
            (rotR p_.α ((rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) =
            rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) -
            ((rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) := by
        simp [map_sub]; abel
      rw [hrw]
      calc ‖rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) -
              ((rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i))‖
        _ ≤ ‖rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i))‖ +
            ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := norm_sub_le _ _
        _ = ‖(rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)‖ +
            ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := by
          rw [Bounding.rotR_preserves_norm]
        _ ≤ (2 * κ + κ ^ 2) + (2 * κ + κ ^ 2) := add_le_add h₁ h₂
        _ = 4 * κ + 2 * κ ^ 2 := by ring
    show δ ≥ ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ / 2
    have hnorm_le : ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ ≤
        ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + (4 * κ + 2 * κ ^ 2) := by
      linarith [norm_le_insert' (p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i))
        (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i))]
    have h6k : 4 * κ + 2 * κ ^ 2 ≤ 6 * κ := by unfold κ; norm_num
    linarith [hsu]
  -- Bridge: Bεℚ → Bε
  have be' : Triangle.Bε Q Qi poly.vertices.v p_ ε δ r := by
    intro i k hne_k
    -- Map k to v_ in poly_
    let k' := hpoly.bijection k
    set v_ : ℝ³ := poly_.toReal.v k'
    have hvapprox : ‖poly.vertices.v k - v_‖ ≤ κ := hpoly.approx k
    have hvnorm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
    -- Get the Bεℚ hypothesis
    have hbe := be i k hne_k
    show (δ + √5 * ε) / r < Local.Triangle.Bε.lhs (Q i) (poly.vertices.v k) p_ ε
    -- Helper facts
    have hκ_pos : (0 : ℝ) < κ := by unfold κ; norm_num
    have hsu_ge : su.norm (Q_ i - v_) ≥ ‖Q_ i - v_‖ := UpperSqrt_norm_le su _
    -- Denominator positivity (su.norm ≥ ‖·‖ ≥ 0, and √2*ε + 3κ > 0)
    have hden_pos : 0 < (su.norm (p_.rotM₂ℚℝ (Q_ i)) + √2 * ε + 3 * κ) *
        (su.norm (p_.rotM₂ℚℝ (Q_ i - v_)) + 2 * √2 * ε + 6 * κ) := by
      have h₁ := le_trans (norm_nonneg (p_.rotM₂ℚℝ (Q_ i))) (UpperSqrt_norm_le su _)
      have h₂ := le_trans (norm_nonneg (p_.rotM₂ℚℝ (Q_ i - v_))) (UpperSqrt_norm_le su _)
      positivity
    -- Extract positivity of Bεℚ numerator
    have hBεℚ_num_pos : 0 < ⟪p_.rotM₂ℚℝ (Q_ i), p_.rotM₂ℚℝ (Q_ i - v_)⟫ - 10 * κ -
        2 * ε * (su.norm (Q_ i - v_) + 2 * κ) * (√2 + ε) := by
      have hδ_pos : 0 < (δ : ℝ) := by
        have hδ₀ := hδ 0
        linarith [le_trans (norm_nonneg _)
           (UpperSqrt_norm_le su (p_.rotR (p_.rotM₁ℚℝ (P_ 0)) - p_.rotM₂ℚℝ (Q_ 0)))]
      have h0 : 0 < (δ + √5 * ε) / r := by positivity
      exact (div_pos_iff_of_pos_right hden_pos).mp (h0.trans hbe)
    -- su.norm ≥ ‖·‖ means numBεℚ ≤ numAℚ (subtracted term is bigger with su.norm)
    have hAℚ_num_pos : 0 < ⟪(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i), (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i - v_)⟫ - 10 * κ -
        2 * ε * (‖Q_ i - v_‖ + 2 * κ) * (√2 + ε) := by
      show 0 < ⟪p_.rotM₂ℚℝ (Q_ i), p_.rotM₂ℚℝ (Q_ i - v_)⟫ - 10 * κ -
          2 * ε * (‖Q_ i - v_‖ + 2 * κ) * (√2 + ε)
      have h_sub_le : 2 * ε * (‖Q_ i - v_‖ + 2 * κ) * (√2 + ε) ≤
          2 * ε * (su.norm (Q_ i - v_) + 2 * κ) * (√2 + ε) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (by grw [hsu_ge]) (by linarith)
        · positivity
      linarith [hBεℚ_num_pos]
    -- From inner_product_bound_10kappa: |innerA - innerAℚ| ≤ 10κ
    have hQv_norm : ‖Q i - poly.vertices.v k‖ ≤ 2 := calc
      ‖Q i - poly.vertices.v k‖ ≤ ‖Q i‖ + ‖poly.vertices.v k‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hQnorm i) hvnorm
      _ = 2 := by ring
    have hQv_approx : ‖(Q i - poly.vertices.v k) - (Q_ i - v_)‖ ≤ 2 * κ := calc
      ‖(Q i - poly.vertices.v k) - (Q_ i - v_)‖ = ‖(Q i - Q_ i) - (poly.vertices.v k - v_)‖ := by congr 1; abel
      _ ≤ ‖Q i - Q_ i‖ + ‖poly.vertices.v k - v_‖ := norm_sub_le _ _
      _ ≤ κ + κ := add_le_add (hQapprox i) hvapprox
      _ = 2 * κ := by ring
    have h_inner_10 : |⟪(rotM ↑θ₂ ↑φ₂) (Q i), (rotM ↑θ₂ ↑φ₂) (Q i - poly.vertices.v k)⟫ -
        ⟪(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i), (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i - v_)⟫| ≤ 10 * κ :=
      inner_product_bound_10kappa (θ := θ₂) (φ := φ₂) (hQnorm i) hQv_norm (hQapprox i) hQv_approx
    have h_norm_QR : ‖Q i - poly.vertices.v k‖ ≤ ‖Q_ i - v_‖ + 2 * κ :=
      calc ‖Q i - poly.vertices.v k‖
        _ ≤ ‖Q_ i - v_‖ + ‖(Q i - poly.vertices.v k) - (Q_ i - v_)‖ := norm_le_insert' _ _
        _ ≤ ‖Q_ i - v_‖ + 2 * κ := by grw [hQv_approx]
    have hA_nonneg : 0 ≤ ⟪(rotM ↑θ₂ ↑φ₂) (Q i), (rotM ↑θ₂ ↑φ₂) (Q i - poly.vertices.v k)⟫ -
        2 * ε * ‖Q i - poly.vertices.v k‖ * (√2 + ε) := by
      have h_inner_le : ⟪(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i), (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i - v_)⟫ - 10 * κ ≤
          ⟪(rotM ↑θ₂ ↑φ₂) (Q i), (rotM ↑θ₂ ↑φ₂) (Q i - poly.vertices.v k)⟫ :=
        sub_le_of_abs_sub_le_left h_inner_10
      have h_eps_term : 2 * ε * ‖Q i - poly.vertices.v k‖ * (√2 + ε) ≤
          2 * ε * (‖Q_ i - v_‖ + 2 * κ) * (√2 + ε) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left h_norm_QR (by linarith)
        · positivity
      linarith [hAℚ_num_pos]
    -- Apply bounds_kappa4 (note: P Q P_ Q_ θ φ are explicit in bounds_kappa4)
    have hbk4 : bounds_kappa4_Aℚ (Q_ i) v_ θ₂ φ₂ ε su ≤
        bounds_kappa4_A (Q i) (poly.vertices.v k) θ₂ φ₂ ε :=
      bounds_kappa4 (Q i) (poly.vertices.v k) (Q_ i) v_ θ₂ φ₂ (hQnorm i) hvnorm (hQapprox i) hvapprox ε hεℝ su hA_nonneg
    -- Bεℚ.lhs ≤ bounds_kappa4_Aℚ (su.norm ≥ ‖·‖ in numerator, denominators def. equal)
    have hBεℚ_le : Local.Triangle.Bεℚ.lhs (Q_ i) v_ p_ ε su ≤
        bounds_kappa4_Aℚ (Q_ i) v_ θ₂ φ₂ ε su := by
      -- Express both sides using p_.rotM₂ℚ (which is def. equal to rotMℚ ↑θ₂ ↑φ₂)
      show (⟪p_.rotM₂ℚℝ (Q_ i), p_.rotM₂ℚℝ (Q_ i - v_)⟫ - 10 * κ -
            2 * ε * (su.norm (Q_ i - v_) + 2 * κ) * (√2 + ε)) /
          ((su.norm (p_.rotM₂ℚℝ (Q_ i)) + √2 * ε + 3 * κ) *
            (su.norm (p_.rotM₂ℚℝ (Q_ i - v_)) + 2 * √2 * ε + 6 * κ)) ≤
          (⟪p_.rotM₂ℚℝ (Q_ i), p_.rotM₂ℚℝ (Q_ i - v_)⟫ - 10 * κ -
            2 * ε * (‖Q_ i - v_‖ + 2 * κ) * (√2 + ε)) /
          ((su.norm (p_.rotM₂ℚℝ (Q_ i)) + √2 * ε + 3 * κ) *
            (su.norm (p_.rotM₂ℚℝ (Q_ i - v_)) + 2 * √2 * ε + 6 * κ))
      apply div_le_div_of_nonneg_right _ (le_of_lt hden_pos)
      have h_sub_le : 2 * ε * (‖Q_ i - v_‖ + 2 * κ) * (√2 + ε) ≤
          2 * ε * (su.norm (Q_ i - v_) + 2 * κ) * (√2 + ε) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (by grw [hsu_ge]) (by linarith)
        · positivity
      grw [h_sub_le]
    -- bounds_kappa4_A = Bε.lhs (definitionally: rotM ↑θ₂ ↑φ₂ = p_.rotM₂)
    have hA_eq : bounds_kappa4_A (Q i) (poly.vertices.v k) θ₂ φ₂ ε = Local.Triangle.Bε.lhs (Q i) (poly.vertices.v k) p_ ε := rfl
    -- Combine
    calc (δ + √5 * ε) / r < Local.Triangle.Bεℚ.lhs (Q_ i) v_ p_ ε su := hbe
      _ ≤ bounds_kappa4_Aℚ (Q_ i) v_ θ₂ φ₂ ε su := hBεℚ_le
      _ ≤ bounds_kappa4_A (Q i) (poly.vertices.v k) θ₂ φ₂ ε := hbk4
      _ = Local.Triangle.Bε.lhs (Q i) (poly.vertices.v k) p_ ε := hA_eq
  -- Apply local_theorem
  exact Local.local_theorem poly Pi Qi cong_tri p_ ε δ r hεℝ hr
    hr₁' hδ' ae₁' ae₂' span₁' span₂' be'
