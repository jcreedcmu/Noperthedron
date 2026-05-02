import Noperthedron.Local
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.EpsKapSpanning
import Noperthedron.RationalApprox.BoundsKappa3
import Noperthedron.RationalApprox.BoundsKappa4

open Local (Triangle)
open scoped RealInnerProductSpace Real

open RationalApprox (κ κℚ UpperSqrt)

namespace Local

def TriangleQ : Type := Fin 3 → Fin 3 → ℚ

def TriangleQ.toReal (t : TriangleQ) : Triangle :=
  fun i => toR3 (t i)

def TriangleQ.Aεℚσ (X : Fin 3 → ℚ) (P_ : TriangleQ) (ε : ℚ) (σ : ℕ)
    (approx : RationalApprox.Approx) : Prop :=
  ∀ i : Fin 3, (-1)^σ * X ⬝ᵥ P_ i > approx.upper_sqrt_two * ε + 3 * κℚ
deriving Decidable

/--
Condition A_ε^ℚ from [SY25] Theorem 48
-/
def TriangleQ.Aεℚ (X : Fin 3 → ℚ) (P_ : TriangleQ) (ε : ℚ) (approx : RationalApprox.Approx) : Prop :=
  ∃ σ ∈ ({0, 1} : Set ℕ), TriangleQ.Aεℚσ X P_ ε σ approx

def TriangleQ.Bεℚ.lhs (v₁ v₂ : Fin 3 → ℚ) (p : Pose ℚ) (ε : ℚ)
   (approx : RationalApprox.Approx) : ℚ :=
   (p.rotM₂ℚ v₁ ⬝ᵥ p.rotM₂ℚ (v₁ - v₂) - 10 * κℚ - 2 * ε * (approx.upper_sqrt.norm (v₁ - v₂) + 2 * κℚ) * (approx.upper_sqrt_two + ε))
   / ((approx.upper_sqrt.norm (p.rotM₂ℚ v₁) + approx.upper_sqrt_two * ε + 3 * κℚ) * (approx.upper_sqrt.norm (p.rotM₂ℚ (v₁ - v₂)) + 2 * approx.upper_sqrt_two * ε + 6 * κℚ))

/--
Condition B_ε^ℚ from [SY25] Theorem 48
-/
def TriangleQ.Bεℚ {ι : Type} [Fintype ι] [DecidableEq ι] (Q_ : TriangleQ) (Qi : Fin 3 → ι)
    (v_ : ι → Fin 3 → ℚ) (p : Pose ℚ) (ε δ r : ℚ) (approx : RationalApprox.Approx) : Prop :=
  ∀ i : Fin 3, ∀ k : ι, k ≠ Qi i →
    (δ + approx.upper_sqrt_five * ε) / r < TriangleQ.Bεℚ.lhs (Q_ i) (v_ k) p ε approx
deriving Decidable

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

/-! ### Universal bridge lemmas between the rational `Fin n → ℚ` and real `ℝⁿ` worlds. -/

private lemma cast_κℚ : ((κℚ : ℚ) : ℝ) = κ := by unfold κℚ κ; norm_num

private lemma toR3_sub (v w : Fin 3 → ℚ) : toR3 (v - w) = toR3 v - toR3 w := by
  unfold toR3; ext i; simp

private lemma toR2_sub (v w : Fin 2 → ℚ) : toR2 (v - w) = toR2 v - toR2 w := by
  unfold toR2; ext i; simp

private lemma toR3_vecXℚ (θ φ : ℚ) : toR3 (vecXℚ θ φ) = vecXℚℝ (↑θ : ℝ) ↑φ := by
  ext j; unfold toR3 vecXℚ vecXℚℝ
  fin_cases j <;> simp [sinℚ_match, cosℚ_match]

private lemma inner_toR3 (v w : Fin 3 → ℚ) :
    @inner ℝ ℝ³ _ (toR3 v) (toR3 w) = ((v ⬝ᵥ w : ℚ) : ℝ) := by
  unfold toR3
  have h := EuclideanSpace.inner_eq_star_dotProduct
    (WithLp.toLp 2 (fun i => (v i : ℝ)) : EuclideanSpace ℝ (Fin 3))
    (WithLp.toLp 2 (fun i => (w i : ℝ)))
  simp only [star_trivial] at h
  rw [show @inner ℝ _ _ (WithLp.toLp 2 (fun i => (v i : ℝ)))
       (WithLp.toLp 2 (fun i => (w i : ℝ))) =
       (fun i => (w i : ℝ)) ⬝ᵥ (fun i => (v i : ℝ)) from h, dotProduct_comm]
  simp [dotProduct]

private lemma inner_toR2 (v w : Fin 2 → ℚ) :
    @inner ℝ ℝ² _ (toR2 v) (toR2 w) = ((v ⬝ᵥ w : ℚ) : ℝ) := by
  unfold toR2
  have h := EuclideanSpace.inner_eq_star_dotProduct
    (WithLp.toLp 2 (fun i => (v i : ℝ)) : EuclideanSpace ℝ (Fin 2))
    (WithLp.toLp 2 (fun i => (w i : ℝ)))
  simp only [star_trivial] at h
  rw [show @inner ℝ _ _ (WithLp.toLp 2 (fun i => (v i : ℝ)))
       (WithLp.toLp 2 (fun i => (w i : ℝ))) =
       (fun i => (w i : ℝ)) ⬝ᵥ (fun i => (v i : ℝ)) from h, dotProduct_comm]
  simp [dotProduct]

private lemma castℝ_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) :
    (fun i => ((M.mulVec v) i : ℝ)) =
      (M.map (fun x => (x : ℝ))).mulVec (fun i => (v i : ℝ)) := by
  ext i; push_cast [Matrix.mulVec, dotProduct]; rfl

private lemma rotMℚ_mat_castℝ (θ φ : ℚ) :
    (rotMℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMℚ_mat, sinℚ_match, cosℚ_match]

private lemma rotRℚ_mat_castℝ (α : ℚ) :
    (rotRℚ_mat (α : ℝ)) = (rotRℚ_mat α).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotRℚ_mat, sinℚ_match, cosℚ_match]

private lemma toR2_rotMℚ (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMℚ θ φ v) = rotMℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) := by
  unfold rotMℚ rotMℚℝ toR2 toR3
  rw [Matrix.toLin'_apply]
  show WithLp.toLp 2 (fun i : Fin 2 => (((rotMℚ_mat θ φ).mulVec v) i : ℝ)) =
       (rotMℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin.toContinuousLinearMap
         (WithLp.toLp 2 (fun i : Fin 3 => (v i : ℝ)))
  rw [castℝ_mulVec, ← rotMℚ_mat_castℝ]
  show WithLp.toLp 2 ((rotMℚ_mat (θ : ℝ) (φ : ℝ)).mulVec _) =
       (rotMℚ_mat (θ : ℝ) (φ : ℝ)).toEuclideanLin
         (WithLp.toLp 2 (fun i : Fin 3 => (v i : ℝ)))
  rw [Matrix.toLpLin_apply]

private lemma toR2_rotRℚ (α : ℚ) (v : Fin 2 → ℚ) :
    toR2 (rotRℚ α v) = rotRℚℝ (α : ℝ) (toR2 v) := by
  unfold rotRℚ rotRℚℝ toR2
  rw [Matrix.toLin'_apply]
  show WithLp.toLp 2 (fun i : Fin 2 => (((rotRℚ_mat α).mulVec v) i : ℝ)) =
       (rotRℚ_mat (α : ℝ)).toEuclideanLin.toContinuousLinearMap
         (WithLp.toLp 2 (fun i : Fin 2 => (v i : ℝ)))
  rw [castℝ_mulVec, ← rotRℚ_mat_castℝ]
  show WithLp.toLp 2 ((rotRℚ_mat (α : ℝ)).mulVec _) =
       (rotRℚ_mat (α : ℝ)).toEuclideanLin
         (WithLp.toLp 2 (fun i : Fin 2 => (v i : ℝ)))
  rw [Matrix.toLpLin_apply]

private lemma toR2_pose_rotM₂ℚ (p : Pose ℚ) (v : Fin 3 → ℚ) :
    toR2 (p.rotM₂ℚ v) = p.toReal.rotM₂ℚℝ (toR3 v) :=
  toR2_rotMℚ p.θ₂ p.φ₂ v

private lemma toR2_pose_rotM₁ℚ (p : Pose ℚ) (v : Fin 3 → ℚ) :
    toR2 (p.rotM₁ℚ v) = p.toReal.rotM₁ℚℝ (toR3 v) :=
  toR2_rotMℚ p.θ₁ p.φ₁ v

private lemma toR2_pose_rotRℚ (p : Pose ℚ) (v : Fin 2 → ℚ) :
    toR2 (p.rotRℚ v) = p.toReal.rotRℚℝ (toR2 v) :=
  toR2_rotRℚ p.α v

/--
Helper used inside `rational_local`'s `Aε` bridge: rephrases the rational
"angle" inequality on the real side, common to `ae₁'` and `ae₂'`.
-/
private lemma aε_bridge {θ φ : ℚ} {ε : ℚ} {approx : Approx}
    (T : Local.TriangleQ) (R : Triangle)
    (hθ : (θ : ℝ) ∈ Set.Icc (-4 : ℝ) 4) (hφ : (φ : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hRnorm : ∀ i : Fin 3, ‖R i‖ ≤ 1)
    (hRapprox : ∀ i : Fin 3, ‖R i - toR3 (T i)‖ ≤ κ)
    (hAε : T.Aεℚ (vecXℚ θ φ) ε approx)
    (hεℝ : 0 < (ε : ℝ)) :
    R.Aε (vecX (θ : ℝ) (φ : ℝ)) ε := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := hAε
  refine ⟨σ, hσ₁, fun i => ?_⟩
  set θsub : Set.Icc (-4 : ℝ) 4 := ⟨(θ : ℝ), hθ⟩
  set φsub : Set.Icc (-4 : ℝ) 4 := ⟨(φ : ℝ), hφ⟩
  have hX : ‖⟪vecX (θsub : ℝ) (φsub : ℝ), R i⟫ -
            ⟪vecXℚℝ (θsub : ℝ) (φsub : ℝ), toR3 (T i)⟫‖ ≤ 3 * κ :=
    bounds_kappa3_X (θ := θsub) (φ := φsub) (hRnorm i) (hRapprox i)
  have h_inner_eq :
      @inner ℝ ℝ³ _ (vecXℚℝ (θ : ℝ) (φ : ℝ)) (toR3 (T i)) =
        (((vecXℚ θ φ) ⬝ᵥ T i : ℚ) : ℝ) := by
    rw [← toR3_vecXℚ]; exact inner_toR3 _ _
  have hσ₂i : (-1) ^ σ * ⟪vecXℚℝ (θ : ℝ) (φ : ℝ), toR3 (T i)⟫ >
      approx.upper_sqrt_two * ε + 3 * κ := by
    rw [h_inner_eq, ← cast_κℚ,
        show ((-1 : ℝ)) ^ σ = ((((-1 : ℚ)) ^ σ : ℚ) : ℝ) by push_cast; rfl]
    exact_mod_cast hσ₂ i
  have h_us2_eps : (√2 : ℝ) * ε ≤ approx.upper_sqrt_two * ε :=
    mul_le_mul_of_nonneg_right approx.upper_sqrt_two_gt_sqrt_two.le hεℝ.le
  rw [Real.norm_eq_abs] at hX
  have habs : |(-1 : ℝ) ^ σ| = 1 := abs_neg_one_pow σ
  have hdiff : |(-1 : ℝ) ^ σ * (⟪vecX (θ : ℝ) (φ : ℝ), R i⟫ -
                                  ⟪vecXℚℝ (θ : ℝ) (φ : ℝ), toR3 (T i)⟫)| ≤ 3 * κ := by
    rw [abs_mul, habs, one_mul]; exact hX
  rw [abs_le] at hdiff
  linarith [hdiff.1,
    mul_sub ((-1 : ℝ) ^ σ) ⟪vecX (θ : ℝ) (φ : ℝ), R i⟫
      ⟪vecXℚℝ (θ : ℝ) (φ : ℝ), toR3 (T i)⟫]


abbrev BoundDeltaℚi (p : Pose ℚ) (P_ Q_ : Local.TriangleQ) (approx : Approx) (i : Fin 3) : ℚ :=
  approx.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ (P_ i)) - p.rotM₂ℚ (Q_ i)) / 2 + 3 * κℚ

/-- The condition on δ -/
def BoundDeltaℚ (δ : ℚ) (p : Pose ℚ) (P_ Q_ : Local.TriangleQ) (approx : Approx) : Prop :=
  ∀ i : Fin 3, δ ≥ BoundDeltaℚi p P_ Q_ approx i
deriving Decidable

/-- The condition on r -/
def BoundRℚ (r ε : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (approx : Approx) : Prop :=
  ∀ i : Fin 3, approx.lower_sqrt.norm (p.rotM₂ℚ (Q_ i)) > r + approx.upper_sqrt_two * ε + 3 * κℚ
deriving Decidable

/--
[SY25] Theorem 48 "The Rational Local Theorem"
-/
theorem rational_local {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (hpoly : κApproxPoly poly.vertices poly_)
    (Pi Qi : Fin 3 → ι)
    (cong_tri : Triangle.Congruent (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi))
    (p_ : Pose ℚ) (hp : p_ ∈ fourInterval ℚ)
    (ε δ r : ℚ) (hε : 0 < ε) (hr : 0 < r)
    (approx : Approx)
    (hr₁ : BoundRℚ r ε p_ (hpoly.transportTri Qi) approx)
    (hδ : BoundDeltaℚ δ p_ (hpoly.transportTri Pi) (hpoly.transportTri Qi) approx)
    (ae₁ : (hpoly.transportTri Pi).Aεℚ p_.vecX₁ℚ ε approx)
    (ae₂ : (hpoly.transportTri Qi).Aεℚ p_.vecX₂ℚ ε approx)
    (span₁ : (hpoly.transportTri Pi).toReal.κSpanning (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) ε)
    (span₂ : (hpoly.transportTri Qi).toReal.κSpanning (p_.θ₂ : ℝ) (p_.φ₂ : ℝ) ε)
    (be : Local.TriangleQ.Bεℚ (hpoly.transportTri Qi) Qi
          (fun k => poly_.v (hpoly.bijection k)) p_ ε δ r approx)
    : ¬∃ p ∈ Metric.closedBall p_.toReal ε, RupertPose p poly.hull := by
  have hεℝ : 0 < (ε : ℝ) := span₁.pos
  -- Keep a handle on the rational pose before shadowing.
  let p_ℚ : Pose ℚ := p_
  set p_ := p_.toReal
  have hp : (fourInterval ℝ).contains p_ := fourInterval_contains_toReal hp
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
    ek_spanning_imp_e_spanning P P_ hPapprox hPnorm hp.θ₁Bound hp.φ₁Bound span₁
  have span₂' : Q.Spanning p_.θ₂ p_.φ₂ ε :=
    ek_spanning_imp_e_spanning Q Q_ hQapprox hQnorm hp.θ₂Bound hp.φ₂Bound span₂
  -- Universal bridges (above) provide the rational ↔ real cast facts we need.
  have h_upper_norm_toR3 : ∀ (v : Fin 3 → ℚ),
      (approx.upper_sqrt.norm v : ℝ) ≥ ‖toR3 v‖ := fun v =>
    UpperSqrt_norm_le approx.upper_sqrt v
  have h_upper_norm_toR2 : ∀ (v : Fin 2 → ℚ),
      (approx.upper_sqrt.norm v : ℝ) ≥ ‖toR2 v‖ := fun v =>
    UpperSqrt_norm_le approx.upper_sqrt v
  -- Main bridge: rewrite `Bεℚ.lhs` in terms of explicit real-form expressions.
  have h_Bεℚ_lhs_bridge : ∀ (v₁ v₂ : Fin 3 → ℚ),
      Local.TriangleQ.Bεℚ.lhs v₁ v₂ p_ℚ ε approx =
      (⟪p_.rotM₂ℚℝ (toR3 v₁), p_.rotM₂ℚℝ (toR3 v₁ - toR3 v₂)⟫ - 10 * κ -
         2 * ε * ((approx.upper_sqrt.norm (v₁ - v₂) : ℝ) + 2 * κ) *
           (approx.upper_sqrt_two + ε)) /
      (((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ v₁) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
       ((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ (v₁ - v₂)) : ℝ) +
          2 * approx.upper_sqrt_two * ε + 6 * κ)) := by
    intro v₁ v₂
    unfold Local.TriangleQ.Bεℚ.lhs
    push_cast [← cast_κℚ]
    rw [show ((p_ℚ.rotM₂ℚ v₁ ⬝ᵥ p_ℚ.rotM₂ℚ (v₁ - v₂) : ℚ) : ℝ) =
        ⟪p_.rotM₂ℚℝ (toR3 v₁), p_.rotM₂ℚℝ (toR3 v₁ - toR3 v₂)⟫ from by
      rw [← toR3_sub, ← toR2_pose_rotM₂ℚ, ← toR2_pose_rotM₂ℚ, inner_toR2]]
  have h_us2_eps : (√2 : ℝ) * ε ≤ approx.upper_sqrt_two * ε :=
    mul_le_mul_of_nonneg_right approx.upper_sqrt_two_gt_sqrt_two.le hεℝ.le
  have ae₁' : P.Aε p_.vecX₁ ε :=
    aε_bridge (T := hpoly.transportTri Pi) (R := P) hp.θ₁Bound hp.φ₁Bound
      hPnorm hPapprox ae₁ hεℝ
  have ae₂' : Q.Aε p_.vecX₂ ε :=
    aε_bridge (T := hpoly.transportTri Qi) (R := Q) hp.θ₂Bound hp.φ₂Bound
      hQnorm hQapprox ae₂ hεℝ
  -- Bridge: BoundRℚ → BoundR
  have hr₁' : Local.BoundR r ε p_ Q := by
    intro i
    have h_toR2_eq : (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i) =
        toR2 (p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) :=
      (toR2_pose_rotM₂ℚ _ _).symm
    have hsl : (approx.lower_sqrt.norm (p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) : ℝ) ≤
        ‖(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := by
      rw [h_toR2_eq]; exact LowerSqrt_norm_ge approx.lower_sqrt _
    have hMQ : |(‖(rotM ↑θ₂ ↑φ₂) (Q i)‖ - ‖(rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖)| ≤ 3 * κ :=
      bounds_kappa3_MQ (θ := θ₂) (φ := φ₂) (hQnorm i) (hQapprox i)
    show ‖(rotM ↑θ₂ ↑φ₂) (Q i)‖ > r + √2 * ε
    have hr₁i : (approx.lower_sqrt.norm (p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) : ℝ) >
        r + √2 * ε + 3 * κ := by
      have hcast : ((approx.lower_sqrt.norm (p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) : ℚ) : ℝ) >
          ((r + approx.upper_sqrt_two * ε + 3 * κℚ : ℚ) : ℝ) := by exact_mod_cast hr₁ i
      push_cast [cast_κℚ] at hcast
      linarith [h_us2_eps]
    rw [abs_le] at hMQ
    linarith [hMQ.1]
  have hδ' : Local.BoundDelta δ p_ P Q := by
    intro i
    have hδi := hδ i
    -- su.norm ≥ ‖·‖ (rational form, then convert to real with toR2)
    have h_eq_real :
        toR2 (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ ((hpoly.transportTri Pi) i)) -
              p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) =
        p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i) := by
      rw [toR2_sub, toR2_pose_rotRℚ, toR2_pose_rotM₁ℚ, toR2_pose_rotM₂ℚ]; rfl
    have hsu : ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ ≤
        (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ ((hpoly.transportTri Pi) i)) -
            p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) : ℝ) := by
      rw [← h_eq_real]; exact UpperSqrt_norm_le approx.upper_sqrt _
    -- ‖p_.rotR (rotM₁ℚℝ P_) - rotRℚℝ (rotM₁ℚℝ P_)‖ ≤ κ * (1 + κ)  (rotR vs rotRℚℝ discrepancy)
    have h_rotRdiff : ‖p_.rotR - p_.rotRℚℝ‖ ≤ κ := R_difference_norm_bounded p_.α hp.αBound
    have hκ_nn : (0 : ℝ) ≤ κ := by unfold κ; norm_num
    have h_rotM₁ℚ_norm : ‖p_.rotM₁ℚℝ (P_ i)‖ ≤ (1 + κ) * (1 + κ) :=
      approx_image_norm_le (Mℚ_norm_bounded θ₁.property φ₁.property) (hPnorm i) (hPapprox i)
    have h_rotR_diff_apply : ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))‖ ≤
        κ * ((1 + κ) * (1 + κ)) := by
      have := ContinuousLinearMap.le_opNorm (p_.rotR - p_.rotRℚℝ) (p_.rotM₁ℚℝ (P_ i))
      simp only [ContinuousLinearMap.sub_apply] at this
      exact this.trans (mul_le_mul h_rotRdiff h_rotM₁ℚ_norm (norm_nonneg _) (by linarith))
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
    show (δ : ℝ) ≥ ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ / 2
    have hnorm_le : ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ ≤
        ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + (4 * κ + 2 * κ ^ 2) := by
      linarith [norm_le_insert' (p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i))
        (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i))]
    -- Bridge `p_.rotR` to `p_.rotRℚℝ` introducing extra κ-slack.
    have h_rotR_to_rotRℚℝ : ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ ≤
        ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + κ * ((1 + κ) * (1 + κ)) := by
      have h_diff_eq : p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i) =
          (p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)) +
          (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))) := by abel
      rw [h_diff_eq]
      calc ‖(p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)) +
            (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)))‖
        _ ≤ ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ +
            ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))‖ := norm_add_le _ _
        _ ≤ ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + κ * ((1 + κ) * (1 + κ)) := by
            linarith [h_rotR_diff_apply]
    have h_total_slack : κ * ((1 + κ) * (1 + κ)) + (4 * κ + 2 * κ ^ 2) ≤ 6 * κ := by
      unfold κ; norm_num
    -- Combine everything.
    have h_chain : ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ ≤
        (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ ((hpoly.transportTri Pi) i)) -
            p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) : ℝ) + 6 * κ := by
      linarith [hsu, hnorm_le, h_rotR_to_rotRℚℝ, h_total_slack]
    -- Now use hδi: δ ≥ s.norm(...) / 2 + 3 * κℚ in ℚ
    have hδiℝ : (δ : ℝ) ≥
        (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ ((hpoly.transportTri Pi) i)) -
            p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) : ℝ) / 2 + 3 * κ := by
      have hcast : ((approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ ((hpoly.transportTri Pi) i)) -
            p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) i)) / 2 + 3 * κℚ : ℚ) : ℝ) ≤ (δ : ℝ) := by
        exact_mod_cast hδi
      push_cast [cast_κℚ] at hcast
      linarith
    linarith [hδiℝ, h_chain]
  -- Bridge: Bεℚ → Bε
  have be' : Triangle.Bε Q Qi poly.vertices.v p_ ε δ r := by
    intro i k hne_k
    -- Map k to v_ in poly_
    let k' := hpoly.bijection k
    let v_ℚ : Fin 3 → ℚ := poly_.v k'
    set v_ : ℝ³ := poly_.toReal.v k'
    have hvapprox : ‖poly.vertices.v k - v_‖ ≤ κ := hpoly.approx k
    have hvnorm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
    -- The rational forms of Q_ i and v_ (definitionally equal via toR3).
    let Q_ℚ : Fin 3 → ℚ := (hpoly.transportTri Qi) i
    -- Get the Bεℚ hypothesis
    have hbe := be i k hne_k
    show (δ + √5 * ε) / r < Local.Triangle.Bε.lhs (Q i) (poly.vertices.v k) p_ ε
    -- Use the bridge to rewrite `Bεℚ.lhs` into explicit real form.
    have h_bridge_Qv := h_Bεℚ_lhs_bridge Q_ℚ v_ℚ
    -- Bridge from approx.upper_sqrt_five to √5 (since upper_sqrt_five > √5)
    have hbe' : (↑δ + √5 * ↑ε) / ↑r <
        (⟪p_.rotM₂ℚℝ (toR3 Q_ℚ), p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)⟫ - 10 * κ -
           2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε)) /
        (((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ Q_ℚ) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
         ((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ)) : ℝ) + 2 * approx.upper_sqrt_two * ε + 6 * κ)) := by
      rw [← h_bridge_Qv]
      have h_le : (↑δ + √5 * ↑ε) / ↑r ≤ (↑δ + ↑approx.upper_sqrt_five * ↑ε) / ↑r := by
        gcongr
        exact approx.upper_sqrt_five_gt_sqrt_five.le
      have hbe_ℝ : ((δ + approx.upper_sqrt_five * ε) / r : ℝ) <
          (Local.TriangleQ.Bεℚ.lhs Q_ℚ v_ℚ p_ℚ ε approx : ℝ) := mod_cast hbe
      push_cast at hbe_ℝ
      exact h_le.trans_lt hbe_ℝ
    -- Helper facts
    have hκ_pos : (0 : ℝ) < κ := by unfold κ; norm_num
    -- Bridges relating real and rational norms via UpperSqrt_norm_le.
    have h_toR3_sub_Qv : toR3 (Q_ℚ - v_ℚ) = toR3 Q_ℚ - toR3 v_ℚ := toR3_sub _ _
    have h_norm_Qv_rat : ‖toR3 Q_ℚ - toR3 v_ℚ‖ ≤ (approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) := by
      rw [← h_toR3_sub_Qv]; exact h_upper_norm_toR3 _
    have h_norm_rotM₂_Q : ‖p_.rotM₂ℚℝ (toR3 Q_ℚ)‖ ≤
        (approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ Q_ℚ) : ℝ) := by
      rw [← toR2_pose_rotM₂ℚ]; exact h_upper_norm_toR2 _
    have h_norm_rotM₂_Qv : ‖p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)‖ ≤
        (approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ)) : ℝ) := by
      rw [← h_toR3_sub_Qv, ← toR2_pose_rotM₂ℚ]; exact h_upper_norm_toR2 _
    have h_us2_nn : (0 : ℝ) ≤ approx.upper_sqrt_two :=
      (Real.sqrt_nonneg 2).trans approx.upper_sqrt_two_gt_sqrt_two.le
    have h_us2_le : (√2 : ℝ) ≤ approx.upper_sqrt_two := approx.upper_sqrt_two_gt_sqrt_two.le
    have hsu_norm_nn : (0 : ℝ) ≤ (approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) :=
      (norm_nonneg _).trans h_norm_Qv_rat
    -- Denominator positivity
    have hden_pos : 0 < ((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ Q_ℚ) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
        ((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ)) : ℝ) + 2 * approx.upper_sqrt_two * ε + 6 * κ) := by
      have h₁ := le_trans (norm_nonneg (p_.rotM₂ℚℝ (toR3 Q_ℚ))) h_norm_rotM₂_Q
      have h₂ := le_trans (norm_nonneg (p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ))) h_norm_rotM₂_Qv
      positivity
    -- Extract positivity of Bεℚ numerator
    have hBεℚ_num_pos : 0 < ⟪p_.rotM₂ℚℝ (toR3 Q_ℚ), p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)⟫ - 10 * κ -
        2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε) := by
      have hδ_pos : 0 < (δ : ℝ) := by
        -- δ ≥ s.norm/2 + 3 * κℚ in ℚ, and s.norm ≥ 0 (it bounds a real norm).
        have hsu0 := UpperSqrt_norm_le approx.upper_sqrt
          (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ ((hpoly.transportTri Pi) 0)) -
            p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) 0))
        have hcast := (Rat.cast_le (K := ℝ)).mpr (hδ 0)
        push_cast [cast_κℚ] at hcast
        linarith [(norm_nonneg _).trans hsu0]
      have h0 : 0 < (δ + √5 * ε) / r := by positivity
      refine (div_pos_iff_of_pos_right hden_pos).mp (h0.trans ?_)
      exact hbe'
    -- bounds_kappa4_Aℚ in real form
    have h_num_sub : 2 * (ε : ℝ) * (‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ) * (√2 + ε) ≤
        2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [h_norm_Qv_rat]) (by linarith))
        (by linarith) (by positivity) (by positivity)
    have hAℚ_num_pos : 0 < ⟪p_.rotM₂ℚℝ (toR3 Q_ℚ), p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)⟫ - 10 * κ -
        2 * ε * (‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ) * (√2 + ε) := by
      linarith [hBεℚ_num_pos]
    -- Inner product 10κ-bound and the related real-norm bound for `Q i - v k`
    have hQv_norm : ‖Q i - poly.vertices.v k‖ ≤ 2 := calc
      ‖Q i - poly.vertices.v k‖ ≤ ‖Q i‖ + ‖poly.vertices.v k‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hQnorm i) hvnorm
      _ = 2 := by ring
    have hQv_approx : ‖(Q i - poly.vertices.v k) - (toR3 Q_ℚ - toR3 v_ℚ)‖ ≤ 2 * κ := by
      rw [show toR3 Q_ℚ - toR3 v_ℚ = Q_ i - v_ from rfl]
      calc ‖(Q i - poly.vertices.v k) - (Q_ i - v_)‖
          = ‖(Q i - Q_ i) - (poly.vertices.v k - v_)‖ := by congr 1; abel
        _ ≤ ‖Q i - Q_ i‖ + ‖poly.vertices.v k - v_‖ := norm_sub_le _ _
        _ ≤ κ + κ := add_le_add (hQapprox i) hvapprox
        _ = 2 * κ := by ring
    -- Apply bounds_kappa4
    have h_Q_approx : ‖Q i - toR3 Q_ℚ‖ ≤ κ := hQapprox i
    have h_v_approx : ‖poly.vertices.v k - toR3 v_ℚ‖ ≤ κ := hvapprox
    have hA_nonneg : 0 ≤ ⟪(rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i),
        (rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i - poly.vertices.v k)⟫ -
        2 * ε * ‖Q i - poly.vertices.v k‖ * (√2 + ε) := by
      have h_inner_10 : |⟪(rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i),
            (rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i - poly.vertices.v k)⟫ -
          ⟪p_.rotM₂ℚℝ (toR3 Q_ℚ),
            p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)⟫| ≤ 10 * κ :=
        inner_product_bound_10kappa (θ := θ₂) (φ := φ₂) (hQnorm i) hQv_norm h_Q_approx hQv_approx
      have h_inner_le : ⟪p_.rotM₂ℚℝ (toR3 Q_ℚ),
            p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)⟫ - 10 * κ ≤
          ⟪(rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i),
            (rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i - poly.vertices.v k)⟫ :=
        sub_le_of_abs_sub_le_left h_inner_10
      have h_norm_QR : ‖Q i - poly.vertices.v k‖ ≤ ‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ :=
        calc ‖Q i - poly.vertices.v k‖
          _ ≤ ‖toR3 Q_ℚ - toR3 v_ℚ‖ +
              ‖(Q i - poly.vertices.v k) - (toR3 Q_ℚ - toR3 v_ℚ)‖ := norm_le_insert' _ _
          _ ≤ ‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ := by grw [hQv_approx]
      have h_eps_term : 2 * ε * ‖Q i - poly.vertices.v k‖ * (√2 + ε) ≤
          2 * ε * (‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ) * (√2 + ε) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left h_norm_QR (by linarith)
        · positivity
      linarith [hAℚ_num_pos]
    have hbk4 : bounds_kappa4_Aℚ Q_ℚ v_ℚ p_ℚ ε approx.upper_sqrt ≤
        bounds_kappa4_A (Q i) (poly.vertices.v k) θ₂ φ₂ ε :=
      bounds_kappa4 (Q i) (poly.vertices.v k) Q_ℚ v_ℚ p_ℚ
        hp.θ₂Bound hp.φ₂Bound (hQnorm i) hvnorm h_Q_approx h_v_approx ε hεℝ
        approx.upper_sqrt hA_nonneg
    -- Bridge `Bεℚ.lhs` real form ≤ `bounds_kappa4_Aℚ`
    have hBεℚ_le :
        (⟪p_.rotM₂ℚℝ (toR3 Q_ℚ), p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)⟫ - 10 * κ -
            2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε)) /
          (((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ Q_ℚ) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
            ((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ)) : ℝ) +
              2 * approx.upper_sqrt_two * ε + 6 * κ)) ≤
        bounds_kappa4_Aℚ Q_ℚ v_ℚ p_ℚ ε approx.upper_sqrt := by
      show _ ≤ ((((p_ℚ.rotM₂ℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ) - 10 * κ -
            2 * ε * (‖toR3 (Q_ℚ - v_ℚ)‖ + 2 * κ) * (√2 + ε)) /
        (((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ Q_ℚ) : ℝ) + √2 * ε + 3 * κ) *
         ((approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ)) : ℝ) + 2 * √2 * ε + 6 * κ))
      have h_inner_eq : ((p_ℚ.rotM₂ℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ) : ℚ) : ℝ) =
          ⟪p_.rotM₂ℚℝ (toR3 Q_ℚ), p_.rotM₂ℚℝ (toR3 Q_ℚ - toR3 v_ℚ)⟫ := by
        rw [← toR2_pose_rotM₂ℚ p_ℚ Q_ℚ, ← h_toR3_sub_Qv,
            ← toR2_pose_rotM₂ℚ p_ℚ (Q_ℚ - v_ℚ), inner_toR2]
      have h₁ : (0 : ℝ) ≤ (approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ Q_ℚ) : ℝ) :=
        le_trans (norm_nonneg _) h_norm_rotM₂_Q
      have h₂ : (0 : ℝ) ≤ (approx.upper_sqrt.norm (p_ℚ.rotM₂ℚ (Q_ℚ - v_ℚ)) : ℝ) :=
        le_trans (norm_nonneg _) h_norm_rotM₂_Qv
      have h_us2_eps : (√2 : ℝ) * ε ≤ approx.upper_sqrt_two * ε :=
        mul_le_mul_of_nonneg_right h_us2_le hεℝ.le
      rw [h_inner_eq, h_toR3_sub_Qv]
      refine div_le_div₀ hAℚ_num_pos.le (by linarith [h_num_sub]) (by positivity) ?_
      gcongr
    -- Combine (final step uses defeq `bounds_kappa4_A = Bε.lhs`).
    calc (δ + √5 * ε) / r
        < _ := hbe'
      _ ≤ bounds_kappa4_Aℚ Q_ℚ v_ℚ p_ℚ ε approx.upper_sqrt := hBεℚ_le
      _ ≤ bounds_kappa4_A (Q i) (poly.vertices.v k) θ₂ φ₂ ε := hbk4
  -- Apply local_theorem
  exact Local.local_theorem poly Pi Qi cong_tri p_ ε δ r hεℝ (Rat.cast_pos.mpr hr)
    hr₁' hδ' ae₁' ae₂' span₁' span₂' be'
