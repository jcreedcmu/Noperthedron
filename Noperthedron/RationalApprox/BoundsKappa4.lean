import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.BoundsKappa3
import Noperthedron.RationalApprox.Cast

open scoped RealInnerProductSpace

namespace RationalApprox

variable (P Q P_ Q_ : ℝ³) (θ φ : Set.Icc (-4 : ℝ) 4) (ε : ℝ)

/-!
[SY25] Corollary 51
-/

noncomputable
def bounds_kappa4_A := (⟪rotM θ φ P, rotM θ φ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
  ((‖rotM θ φ P‖ + √2 * ε) * (‖rotM θ φ (P - Q)‖ + 2 * √2 * ε))

noncomputable
def bounds_kappa4_Aℚ (P_ Q_ : Fin 3 → ℚ) (p : Pose ℚ) (ε : ℝ) (s : UpperSqrt) : ℝ :=
  (((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ) - 10 * κ -
      2 * ε * (‖toR3 (P_ - Q_)‖ + 2 * κ) * (√2 + ε)) /
  ((↑(s.norm (p.rotM₂ℚ P_)) + √2 * ε + 3 * κ) *
    (↑(s.norm (p.rotM₂ℚ (P_ - Q_))) + 2 * √2 * ε + 6 * κ))

/-- An `UpperSqrt` overestimates the Euclidean norm of a rational vector cast to `ℝ`. -/
lemma UpperSqrt_norm_le {n : ℕ} (s : UpperSqrt) (v : Fin n → ℚ) :
    ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ ≤ ↑(s.norm v) := by
  unfold UpperSqrt.norm
  have h_norm_sq := toLp_norm_sq_eq_dotProduct v
  have h_dot_nn : (0 : ℝ) ≤ ((v ⬝ᵥ v : ℚ) : ℝ) := by
    rw [← h_norm_sq]; exact sq_nonneg _
  have h_dot_nn_ℚ : (0 : ℚ) ≤ v ⬝ᵥ v := mod_cast h_dot_nn
  calc ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖
      = √(‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ = √(((v ⬝ᵥ v : ℚ) : ℝ)) := by rw [h_norm_sq]
    _ ≤ ↑(s.f (v ⬝ᵥ v)) := s.bound _ h_dot_nn_ℚ

/-- A `LowerSqrt` underestimates the Euclidean norm of a rational vector cast to `ℝ`. -/
lemma LowerSqrt_norm_ge {n : ℕ} (s : LowerSqrt) (v : Fin n → ℚ) :
    ↑(s.norm v) ≤ ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ := by
  unfold LowerSqrt.norm
  have h_norm_sq := toLp_norm_sq_eq_dotProduct v
  have h_dot_nn : (0 : ℝ) ≤ ((v ⬝ᵥ v : ℚ) : ℝ) := by
    rw [← h_norm_sq]; exact sq_nonneg _
  have h_dot_nn_ℚ : (0 : ℚ) ≤ v ⬝ᵥ v := mod_cast h_dot_nn
  calc (↑(s.f (v ⬝ᵥ v)) : ℝ)
      ≤ √(((v ⬝ᵥ v : ℚ) : ℝ)) := s.bound _ h_dot_nn_ℚ
    _ = √(‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ ^ 2) := by rw [h_norm_sq]
    _ = ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ := Real.sqrt_sq (norm_nonneg _)

/-- The inner product bound for `rotM`/`rotMℚ` when the second vector has norm ≤ 2.
This generalises `bounds_kappa3_M` (which requires ‖Q‖ ≤ 1) to handle `P − Q`. -/
lemma inner_product_bound_10kappa
    {P Q P_ Q_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}
    (hP : ‖P‖ ≤ 1) (hR : ‖Q‖ ≤ 2)
    (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ 2 * κ) :
    |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotMℚℝ ↑θ ↑φ) Q_⟫| ≤ 10 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hMℚnorm : ‖rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (θ.property) (φ.property)
  -- Decompose: ⟪rotM P, rotM Q⟫ - ⟪rotMℚ P_, rotMℚ Q_⟫
  --   = ⟪rotM P - rotMℚ P_, rotM Q⟫ + ⟪rotMℚ P_, rotM Q - rotMℚ Q_⟫
  have decomp : ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotMℚℝ ↑θ ↑φ) Q_⟫ =
      ⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
      ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  -- Bound ‖rotM P - rotMℚ P_‖
  have hAP : ‖(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hMdiff hMℚnorm hP Papprox
  -- Bound ‖rotM Q - rotMℚ Q_‖ (with ‖Q‖ ≤ 2 and ‖Q - Q_‖ ≤ 2κ)
  have hBQ : ‖(rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_‖ ≤ 4 * κ + 2 * κ ^ 2 :=
    clm_approx_apply_sub₂ hMdiff hMℚnorm hR Qapprox
  -- Bound ‖rotM Q‖
  have hMQ : ‖(rotM ↑θ ↑φ) Q‖ ≤ 2 := by
    have := ContinuousLinearMap.le_opNorm (rotM ↑θ ↑φ) Q
    rw [Bounding.rotM_norm_one, one_mul] at this; linarith
  -- Bound ‖rotMℚ P_‖
  have hMℚP_ : ‖(rotMℚℝ ↑θ ↑φ) P_‖ ≤ (1 + κ) * (1 + κ) :=
    approx_image_norm_le hMℚnorm hP Papprox
  calc |⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
        ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫|
    _ ≤ |⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫| +
        |⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫| := abs_add_le _ _
    _ ≤ ‖(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q‖ +
        ‖(rotMℚℝ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (2 * κ + κ ^ 2) * 2 + (1 + κ) * (1 + κ) * (4 * κ + 2 * κ ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAP (norm_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left hMQ (by norm_num [κ])))
          (mul_le_mul hMℚP_ hBQ (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 10 * κ := by unfold κ; norm_num

/-- The norm difference bound for `rotM`/`rotMℚ` applied to P (norm ≤ 1).
    Generalises `bounds_kappa3_MQ` from BoundsKappa3.lean. -/
lemma norm_diff_bound_3kappa
    {P P_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}
    (hP : ‖P‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) :
    ‖(rotM ↑θ ↑φ) P‖ ≤ ‖(rotMℚℝ ↑θ ↑φ) P_‖ + 3 * κ := by
  have h := bounds_kappa3_MQ (θ := θ) (φ := φ) hP Papprox
  rw [abs_le] at h
  linarith [h.1]

/-- The norm difference bound for `rotM`/`rotMℚ` applied to `P - Q` (norm ≤ 2).
    Uses the same technique as bounds_kappa3_MQ but for ‖P - Q‖ ≤ 2. -/
lemma norm_diff_bound_6kappa
    {P Q P_ Q_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    ‖(rotM ↑θ ↑φ) (P - Q)‖ ≤ ‖(rotMℚℝ ↑θ ↑φ) (P_ - Q_)‖ + 6 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hMℚnorm : ‖rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (θ.property) (φ.property)
  have hPQ_norm : ‖P - Q‖ ≤ 2 := by
    calc ‖P - Q‖ ≤ ‖P‖ + ‖Q‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hP hQ
      _ = 2 := by ring
  have hPQ_approx : ‖(P - Q) - (P_ - Q_)‖ ≤ 2 * κ := by
    calc ‖(P - Q) - (P_ - Q_)‖ = ‖(P - P_) - (Q - Q_)‖ := by congr 1; abel
      _ ≤ ‖P - P_‖ + ‖Q - Q_‖ := norm_sub_le _ _
      _ ≤ κ + κ := add_le_add Papprox Qapprox
      _ = 2 * κ := by ring
  -- ‖M(P-Q) - Mℚ(P_-Q_)‖ ≤ ‖(M-Mℚ)(P-Q)‖ + ‖Mℚ((P-Q)-(P_-Q_))‖
  have h_diff : ‖(rotM ↑θ ↑φ) (P - Q) - (rotMℚℝ ↑θ ↑φ) (P_ - Q_)‖ ≤ 6 * κ :=
    (clm_approx_apply_sub₂ hMdiff hMℚnorm hPQ_norm hPQ_approx).trans (by unfold κ; norm_num)
  linarith [norm_le_insert' ((rotM ↑θ ↑φ) (P - Q)) ((rotMℚℝ ↑θ ↑φ) (P_ - Q_))]

/-- [SY25] Corollary 51 -/
lemma bounds_kappa4 (P Q : ℝ³) (P_ Q_ : Fin 3 → ℚ) (p : Pose ℚ)
    (hθBound : (p.θ₂ : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hφBound : (p.φ₂ : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (Papprox : ‖P - toR3 P_‖ ≤ κ) (Qapprox : ‖Q - toR3 Q_‖ ≤ κ)
    (ε : ℝ) (hε : 0 < ε) (s : UpperSqrt)
    (hA_nonneg : 0 ≤ ⟪rotM (p.θ₂ : ℝ) (p.φ₂ : ℝ) P,
        rotM (p.θ₂ : ℝ) (p.φ₂ : ℝ) (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) :
    bounds_kappa4_Aℚ P_ Q_ p ε s ≤
      bounds_kappa4_A P Q ⟨(p.θ₂ : ℝ), hθBound⟩ ⟨(p.φ₂ : ℝ), hφBound⟩ ε := by
  set θ : Set.Icc (-4 : ℝ) 4 := ⟨(p.θ₂ : ℝ), hθBound⟩
  set φ : Set.Icc (-4 : ℝ) 4 := ⟨(p.φ₂ : ℝ), hφBound⟩
  -- Bridges: link rational dot/norm to real inner/norm.
  have h_toR3_sub : toR3 (P_ - Q_) = toR3 P_ - toR3 Q_ := toR3_sub _ _
  have h_inner_bridge : ((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ) =
      ⟪(rotMℚℝ ↑θ ↑φ) (toR3 P_), (rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)⟫ := by
    rw [← toR2_rotM₂ℚ, ← h_toR3_sub, ← toR2_rotM₂ℚ, inner_toR2]
  have h_norm_bridge_P : ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_)‖ ≤ ↑(s.norm (p.rotM₂ℚ P_)) := by
    rw [← toR2_rotM₂ℚ]
    show ‖toR2 (p.rotM₂ℚ P_)‖ ≤ ↑(s.norm (p.rotM₂ℚ P_))
    exact UpperSqrt_norm_le s _
  have h_norm_bridge_PQ : ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)‖ ≤
      ↑(s.norm (p.rotM₂ℚ (P_ - Q_))) := by
    rw [← h_toR3_sub, ← toR2_rotM₂ℚ]
    show ‖toR2 (p.rotM₂ℚ (P_ - Q_))‖ ≤ ↑(s.norm (p.rotM₂ℚ (P_ - Q_)))
    exact UpperSqrt_norm_le s _
  -- Abbreviate the numerators and denominators
  set numA := ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)
  set numAℚ := ((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ) - 10 * κ -
    2 * ε * (‖toR3 (P_ - Q_)‖ + 2 * κ) * (√2 + ε)
  set denA := (‖(rotM ↑θ ↑φ) P‖ + √2 * ε) * (‖(rotM ↑θ ↑φ) (P - Q)‖ + 2 * √2 * ε)
  set denAℚ := (↑(s.norm (p.rotM₂ℚ P_)) + √2 * ε + 3 * κ) *
    (↑(s.norm (p.rotM₂ℚ (P_ - Q_))) + 2 * √2 * ε + 6 * κ)
  change numAℚ / denAℚ ≤ numA / denA
  -- Step 1: numAℚ ≤ numA
  have h_numAℚ_le : numAℚ ≤ numA := by
    have hPQ_norm : ‖P - Q‖ ≤ 2 := by
      calc ‖P - Q‖ ≤ ‖P‖ + ‖Q‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hP hQ
        _ = 2 := by ring
    have hPQ_approx : ‖(P - Q) - (toR3 P_ - toR3 Q_)‖ ≤ 2 * κ := by
      calc ‖(P - Q) - (toR3 P_ - toR3 Q_)‖
          = ‖(P - toR3 P_) - (Q - toR3 Q_)‖ := by congr 1; abel
        _ ≤ ‖P - toR3 P_‖ + ‖Q - toR3 Q_‖ := norm_sub_le _ _
        _ ≤ κ + κ := add_le_add Papprox Qapprox
        _ = 2 * κ := by ring
    have h_inner_real : |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
        ⟪(rotMℚℝ ↑θ ↑φ) (toR3 P_), (rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)⟫| ≤ 10 * κ :=
      inner_product_bound_10kappa hP hPQ_norm Papprox hPQ_approx
    have h_inner :
        |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
          ((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ)| ≤ 10 * κ := by
      rw [h_inner_bridge]; exact h_inner_real
    replace h_inner := sub_le_of_abs_sub_le_left h_inner
    have h_norm_PQ : ‖P - Q‖ ≤ ‖toR3 (P_ - Q_)‖ + 2 * κ := by
      rw [h_toR3_sub]
      calc ‖P - Q‖
        _ ≤ ‖toR3 P_ - toR3 Q_‖ + ‖(P - Q) - (toR3 P_ - toR3 Q_)‖ := norm_le_insert' _ _
        _ ≤ ‖toR3 P_ - toR3 Q_‖ + 2 * κ := by grw [hPQ_approx]
    have h_eps_term : 2 * ε * ‖P - Q‖ * (√2 + ε) ≤
        2 * ε * (‖toR3 (P_ - Q_)‖ + 2 * κ) * (√2 + ε) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h_norm_PQ (by linarith)) (by positivity)
    linarith [h_inner, h_eps_term]
  -- Step 2: denA ≤ denAℚ
  have h_denA_le : denA ≤ denAℚ := by
    have h_f1 : ‖(rotM ↑θ ↑φ) P‖ + √2 * ε ≤
        ↑(s.norm (p.rotM₂ℚ P_)) + √2 * ε + 3 * κ := by
      have h1 : ‖(rotM ↑θ ↑φ) P‖ ≤ ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_)‖ + 3 * κ :=
        norm_diff_bound_3kappa hP Papprox (θ := θ) (φ := φ)
      linarith [h1, h_norm_bridge_P]
    have h_f2 : ‖(rotM ↑θ ↑φ) (P - Q)‖ + 2 * √2 * ε ≤
        ↑(s.norm (p.rotM₂ℚ (P_ - Q_))) + 2 * √2 * ε + 6 * κ := by
      have h2 : ‖(rotM ↑θ ↑φ) (P - Q)‖ ≤ ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)‖ + 6 * κ :=
        norm_diff_bound_6kappa hP hQ Papprox Qapprox (θ := θ) (φ := φ)
      linarith [h2, h_norm_bridge_PQ]
    exact mul_le_mul h_f1 h_f2 (by positivity) (le_trans (by positivity) h_f1)
  exact div_le_div₀ hA_nonneg h_numAℚ_le (by positivity) h_denA_le
