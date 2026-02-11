import Mathlib.Algebra.Lie.OfAssociative
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.BoundsKappa3

open scoped RealInnerProductSpace

namespace RationalApprox

variable (P Q P_ Q_ : ℝ³) (α θ φ : Set.Icc (-4 : ℝ) 4) (ε : ℝ)

/-!
[SY25] Corollary 51
-/

noncomputable
def bounds_kappa4_A := (⟪rotM θ φ P, rotM θ φ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
  ((‖rotM θ φ P‖ + √2 * ε) * (‖rotM θ φ (P - Q)‖ + 2 * √2 * ε))

noncomputable
def bounds_kappa4_Aℚ (s : UpperSqrt) :=
  (⟪rotMℚ θ φ P_, rotMℚ θ φ (P_ - Q_)⟫ - 10 * κ - 2 * ε * (‖P_ - Q_‖ + 2 * κ) * (√2 + ε)) /
  ((s.norm (rotMℚ θ φ P_) + √2 * ε + 3 * κ) * (s.norm (rotMℚ θ φ (P_ - Q_)) + 2 * √2 * ε + 6 * κ))

/-- An `UpperSqrt` overestimates the Euclidean norm. -/
private lemma UpperSqrt_norm_le {n : ℕ} (s : UpperSqrt) (v : Euc(n)) : ‖v‖ ≤ s.norm v := by
  unfold UpperSqrt.norm
  have h : (0 : ℝ) ≤ ‖v‖ ^ 2 := sq_nonneg _
  calc ‖v‖ = √(‖v‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ s.f (‖v‖ ^ 2) := s.bound _ h

/-- The inner product bound for `rotM`/`rotMℚ` when the second vector has norm ≤ 2.
This generalises `bounds_kappa3_M` (which requires ‖Q‖ ≤ 1) to handle `P − Q`. -/
private lemma inner_product_bound_10kappa
    {P Q P_ Q_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}
    (hP : ‖P‖ ≤ 1) (hR : ‖Q‖ ≤ 2)
    (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ 2 * κ) :
    |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚ ↑θ ↑φ) P_, (rotMℚ ↑θ ↑φ) Q_⟫| ≤ 10 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hMℚnorm : ‖rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (θ.property) (φ.property)
  -- Decompose: ⟪rotM P, rotM Q⟫ - ⟪rotMℚ P_, rotMℚ Q_⟫
  --   = ⟪rotM P - rotMℚ P_, rotM Q⟫ + ⟪rotMℚ P_, rotM Q - rotMℚ Q_⟫
  have decomp : ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚ ↑θ ↑φ) P_, (rotMℚ ↑θ ↑φ) Q_⟫ =
      ⟪(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
      ⟪(rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  -- Bound ‖rotM P - rotMℚ P_‖
  have hAP : ‖(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hMdiff hMℚnorm hP Papprox
  -- Bound ‖rotM Q - rotMℚ Q_‖ (with ‖Q‖ ≤ 2 and ‖Q - Q_‖ ≤ 2κ)
  have hBQ : ‖(rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_‖ ≤ 4 * κ + 2 * κ ^ 2 :=
    clm_approx_apply_sub₂ hMdiff hMℚnorm hR Qapprox
  -- Bound ‖rotM Q‖
  have hMQ : ‖(rotM ↑θ ↑φ) Q‖ ≤ 2 := by
    have := ContinuousLinearMap.le_opNorm (rotM ↑θ ↑φ) Q
    rw [Bounding.rotM_norm_one, one_mul] at this; linarith
  -- Bound ‖rotMℚ P_‖
  have hMℚP_ : ‖(rotMℚ ↑θ ↑φ) P_‖ ≤ (1 + κ) * (1 + κ) :=
    approx_image_norm_le hMℚnorm hP Papprox
  calc |⟪(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
        ⟪(rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_⟫|
    _ ≤ |⟪(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫| +
        |⟪(rotMℚ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_⟫| := abs_add_le _ _
    _ ≤ ‖(rotM ↑θ ↑φ) P - (rotMℚ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q‖ +
        ‖(rotMℚ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q - (rotMℚ ↑θ ↑φ) Q_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (2 * κ + κ ^ 2) * 2 + (1 + κ) * (1 + κ) * (4 * κ + 2 * κ ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAP (norm_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left hMQ (by norm_num [κ])))
          (mul_le_mul hMℚP_ hBQ (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 10 * κ := by unfold κ; norm_num

/-- The norm difference bound for `rotM`/`rotMℚ` applied to P (norm ≤ 1).
    Generalises `bounds_kappa3_MQ` from BoundsKappa3.lean. -/
private lemma norm_diff_bound_3kappa
    {P P_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}
    (hP : ‖P‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) :
    ‖(rotM ↑θ ↑φ) P‖ ≤ ‖(rotMℚ ↑θ ↑φ) P_‖ + 3 * κ := by
  have h := bounds_kappa3_MQ (θ := θ) (φ := φ) hP Papprox
  rw [abs_le] at h
  linarith [h.1]

/-- The norm difference bound for `rotM`/`rotMℚ` applied to `P - Q` (norm ≤ 2).
    Uses the same technique as bounds_kappa3_MQ but for ‖P - Q‖ ≤ 2. -/
private lemma norm_diff_bound_6kappa
    {P Q P_ Q_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ) :
    ‖(rotM ↑θ ↑φ) (P - Q)‖ ≤ ‖(rotMℚ ↑θ ↑φ) (P_ - Q_)‖ + 6 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hMℚnorm : ‖rotMℚ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
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
  have h_diff : ‖(rotM ↑θ ↑φ) (P - Q) - (rotMℚ ↑θ ↑φ) (P_ - Q_)‖ ≤ 6 * κ :=
    (clm_approx_apply_sub₂ hMdiff hMℚnorm hPQ_norm hPQ_approx).trans (by unfold κ; norm_num)
  linarith [norm_le_insert' ((rotM ↑θ ↑φ) (P - Q)) ((rotMℚ ↑θ ↑φ) (P_ - Q_))]

lemma bounds_kappa4 (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ κ)
    (ε : ℝ) (hε : 0 < ε) (s : UpperSqrt)
    (hA_nonneg : 0 ≤ ⟪rotM θ φ P, rotM θ φ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) :
    bounds_kappa4_Aℚ P_ Q_ θ φ ε s ≤ bounds_kappa4_A P Q θ φ ε := by
  -- Abbreviate the numerators and denominators
  set numA := ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε) with numA_def
  set numAℚ := ⟪(rotMℚ ↑θ ↑φ) P_, (rotMℚ ↑θ ↑φ) (P_ - Q_)⟫ - 10 * κ -
    2 * ε * (‖P_ - Q_‖ + 2 * κ) * (√2 + ε) with numAℚ_def
  set denA := (‖(rotM ↑θ ↑φ) P‖ + √2 * ε) * (‖(rotM ↑θ ↑φ) (P - Q)‖ + 2 * √2 * ε)
    with denA_def
  set denAℚ := (s.norm ((rotMℚ ↑θ ↑φ) P_) + √2 * ε + 3 * κ) *
    (s.norm ((rotMℚ ↑θ ↑φ) (P_ - Q_)) + 2 * √2 * ε + 6 * κ) with denAℚ_def
  -- The goal becomes numAℚ / denAℚ ≤ numA / denA after unfolding
  change numAℚ / denAℚ ≤ numA / denA
  -- Step 1: numAℚ ≤ numA
  have h_numAℚ_le : numAℚ ≤ numA := by
    -- First, bound the inner product difference
    have hPQ_norm : ‖P - Q‖ ≤ 2 := by
      calc ‖P - Q‖ ≤ ‖P‖ + ‖Q‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hP hQ
        _ = 2 := by ring
    have hPQ_approx : ‖(P - Q) - (P_ - Q_)‖ ≤ 2 * κ := by
      calc ‖(P - Q) - (P_ - Q_)‖ = ‖(P - P_) - (Q - Q_)‖ := by congr 1; abel
        _ ≤ ‖P - P_‖ + ‖Q - Q_‖ := norm_sub_le _ _
        _ ≤ κ + κ := add_le_add Papprox Qapprox
        _ = 2 * κ := by ring
    have h_inner : |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
        ⟪(rotMℚ ↑θ ↑φ) P_, (rotMℚ ↑θ ↑φ) (P_ - Q_)⟫| ≤ 10 * κ :=
      inner_product_bound_10kappa hP hPQ_norm Papprox hPQ_approx
    -- From |a - b| ≤ 10κ we get b - 10κ ≤ a
    have h_inner_le : ⟪(rotMℚ ↑θ ↑φ) P_, (rotMℚ ↑θ ↑φ) (P_ - Q_)⟫ - 10 * κ ≤
        ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ := by
      rw [abs_le] at h_inner; linarith [h_inner.1]
    -- Bound the norm term: ‖P - Q‖ ≤ ‖P_ - Q_‖ + 2κ
    have h_norm_PQ : ‖P - Q‖ ≤ ‖P_ - Q_‖ + 2 * κ := by
      calc ‖P - Q‖
        _ ≤ ‖P_ - Q_‖ + ‖(P - Q) - (P_ - Q_)‖ := norm_le_insert' _ _
        _ ≤ ‖P_ - Q_‖ + 2 * κ := by linarith [hPQ_approx]
    -- Now combine: numAℚ ≤ numA
    -- numAℚ = inner_ℚ - 10κ - 2ε(‖P_-Q_‖ + 2κ)(√2 + ε)
    -- numA  = inner - 2ε‖P-Q‖(√2 + ε)
    -- We need: inner_ℚ - 10κ - 2ε(‖P_-Q_‖ + 2κ)(√2 + ε) ≤ inner - 2ε‖P-Q‖(√2 + ε)
    -- i.e., inner_ℚ - 10κ ≤ inner + 2ε(√2 + ε)((‖P_-Q_‖ + 2κ) - ‖P-Q‖)
    -- which follows from inner_ℚ - 10κ ≤ inner and (‖P_-Q_‖ + 2κ) - ‖P-Q‖ ≥ 0
    have h_eps_term : 2 * ε * ‖P - Q‖ * (√2 + ε) ≤ 2 * ε * (‖P_ - Q_‖ + 2 * κ) * (√2 + ε) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h_norm_PQ (by linarith)) (by positivity)
    linarith [h_inner_le, h_eps_term]
  -- Step 2: denA > 0
  have h_denA_pos : 0 < denA := by positivity
  -- Step 3: denA ≤ denAℚ
  have h_denA_le : denA ≤ denAℚ := by
    -- Factor 1: ‖rotM P‖ + √2ε ≤ s.norm(rotMℚ P_) + √2ε + 3κ
    have h_f1 : ‖(rotM ↑θ ↑φ) P‖ + √2 * ε ≤
        s.norm ((rotMℚ ↑θ ↑φ) P_) + √2 * ε + 3 * κ := by
      have h1 := norm_diff_bound_3kappa hP Papprox (θ := θ) (φ := φ)
      have h2 := UpperSqrt_norm_le s ((rotMℚ ↑θ ↑φ) P_)
      linarith
    -- Factor 2: ‖rotM (P-Q)‖ + 2√2ε ≤ s.norm(rotMℚ (P_-Q_)) + 2√2ε + 6κ
    have h_f2 : ‖(rotM ↑θ ↑φ) (P - Q)‖ + 2 * √2 * ε ≤
        s.norm ((rotMℚ ↑θ ↑φ) (P_ - Q_)) + 2 * √2 * ε + 6 * κ := by
      have h1 := norm_diff_bound_6kappa hP hQ Papprox Qapprox (θ := θ) (φ := φ)
      have h2 := UpperSqrt_norm_le s ((rotMℚ ↑θ ↑φ) (P_ - Q_))
      linarith
    -- Both factors are nonneg
    have h_f1_nn : 0 ≤ ‖(rotM ↑θ ↑φ) P‖ + √2 * ε := by positivity
    have h_f2_nn : 0 ≤ ‖(rotM ↑θ ↑φ) (P - Q)‖ + 2 * √2 * ε := by positivity
    exact mul_le_mul h_f1 h_f2 h_f2_nn (le_trans h_f1_nn h_f1)
  -- Step 4: Apply div_le_div₀
  exact div_le_div₀ hA_nonneg h_numAℚ_le h_denA_pos h_denA_le
