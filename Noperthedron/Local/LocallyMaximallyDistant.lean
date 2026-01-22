import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.Local.Prelims

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- The intersection of the δ-disc centered at Q with the interior of the convex hull of P -/
def sect (δ : ℝ) (Q : Euc(2)) (P : Finset Euc(2)) : Set Euc(2) :=
  Metric.ball Q δ ∩ interior (convexHull ℝ P)

/--
[SY25] Definition 31
"Q is δ-locally maximally distant with respect to Q_" or "Q is δ-LMD(Q_)".
-/
def LocallyMaximallyDistant (δ : ℝ) (Q Q_ : Euc(2)) (P : Finset Euc(2)) : Prop :=
  ∀ A ∈ sect δ Q_ P, ‖A‖ < ‖Q‖

/--
Key algebraic identity: ‖A‖² - ‖Q‖² = 2⟪Q, A - Q⟫ + ‖A - Q‖²
-/
private lemma norm_sq_diff_eq {A Q : Euc(2)} :
    ‖A‖^2 - ‖Q‖^2 = 2 * ⟪Q, A - Q⟫ + ‖A - Q‖^2 := by
  have h := norm_add_sq_real Q (A - Q)
  simp only [add_sub_cancel] at h
  linarith

/--
If the angle condition holds and Q ≠ 0, then ⟪Q, Pᵢ - Q⟫ is bounded above by a negative quantity.
-/
private lemma inner_toward_vertex_neg {P : Finset Euc(2)} {Q : Euc(2)} {δ r : ℝ}
    (hr : 0 < r) (hrQ : r < ‖Q‖) (Pᵢ : Euc(2)) (hPᵢ : Pᵢ ∈ P) (hne : Pᵢ ≠ Q)
    (hle : δ / r ≤ ⟪Q, Q - Pᵢ⟫ / (‖Q‖ * ‖Q - Pᵢ‖)) :
    ⟪Q, Pᵢ - Q⟫ ≤ -(δ / r) * ‖Q‖ * ‖Q - Pᵢ‖ := by
  have hQ_pos : 0 < ‖Q‖ := lt_trans hr hrQ
  have hQPᵢ_pos : 0 < ‖Q - Pᵢ‖ := norm_sub_pos_iff.mpr hne.symm
  have hdenom_pos : 0 < ‖Q‖ * ‖Q - Pᵢ‖ := mul_pos hQ_pos hQPᵢ_pos
  have h1 : δ / r * (‖Q‖ * ‖Q - Pᵢ‖) ≤ ⟪Q, Q - Pᵢ⟫ := by
    have h := (le_div_iff₀ hdenom_pos).mp hle
    linarith
  have h2 : ⟪Q, Pᵢ - Q⟫ = -⟪Q, Q - Pᵢ⟫ := by simp [inner_sub_right]
  linarith

/--
[SY25] Lemma 32
-/
theorem inner_ge_implies_LMD {P : Finset Euc(2)} {Q Q_ : Euc(2)} {δ r : ℝ}
    (hQ : Q ∈ P) (hQ_ : ‖Q - Q_‖ < δ) (hr : 0 < r) (hrQ : r < ‖Q‖)
    (hle : ∀ Pᵢ ∈ P, Pᵢ ≠ Q → δ / r ≤ ⟪Q, Q - Pᵢ⟫ / (‖Q‖ * ‖Q - Pᵢ‖)) :
    LocallyMaximallyDistant δ Q Q_ P := by
  -- We need to show: for all A in sect δ Q_ P, ‖A‖ < ‖Q‖
  intro A hA
  simp only [sect, Set.mem_inter_iff, Metric.mem_ball] at hA
  obtain ⟨hA_ball, hA_interior⟩ := hA
  -- A is within δ of Q_, and Q is within δ of Q_, so A is within 2δ of Q
  have hAQ : ‖A - Q‖ < 2 * δ := by
    calc ‖A - Q‖ ≤ ‖A - Q_‖ + ‖Q_ - Q‖ := norm_sub_le_norm_sub_add_norm_sub A Q_ Q
    _ = ‖A - Q_‖ + ‖Q - Q_‖ := by rw [norm_sub_rev Q_ Q]
    _ < δ + δ := by
      apply add_lt_add
      · rwa [dist_eq_norm] at hA_ball
      · exact hQ_
    _ = 2 * δ := by ring
  -- The key is to show ‖A‖² < ‖Q‖² using the angle condition
  -- We have: ‖A‖² - ‖Q‖² = 2⟪Q, A - Q⟫ + ‖A - Q‖²
  -- If A is in the interior and close to Q, then ⟪Q, A - Q⟫ should be negative enough
  have hQ_pos : 0 < ‖Q‖ := lt_trans hr hrQ
  -- Show ‖A‖² < ‖Q‖² by showing the difference is negative
  have h_sq_diff : ‖A‖^2 - ‖Q‖^2 < 0 := by
    rw [norm_sq_diff_eq]
    -- Need: 2 * ⟪Q, A - Q⟫ + ‖A - Q‖² < 0
    --
    -- [SY25] Lemma 32 proof outline:
    -- The key geometric insight is that since A is in the interior of the
    -- convex hull and Q is a vertex, A - Q points "into" the polygon.
    -- The angle condition ensures Q "sticks out" enough.
    --
    -- Specifically:
    -- 1. Since Q is a vertex of convexHull P, Q is an extreme point
    -- 2. Since A ∈ interior (convexHull P), A is not on the boundary
    -- 3. The direction A - Q must have ⟪Q, A - Q⟫ < 0 (pointing "inward")
    -- 4. The angle condition quantifies: for each edge direction (Q - Pᵢ),
    --    the cosine ⟪Q, Q - Pᵢ⟫/(‖Q‖ * ‖Q - Pᵢ‖) ≥ δ/r
    -- 5. This implies ⟪Q, Pᵢ - Q⟫ ≤ -(δ/r) * ‖Q‖ * ‖Q - Pᵢ‖ (inward is negative)
    -- 6. Since A - Q is a positive combination of inward directions when A ∈ interior,
    --    we get ⟪Q, A - Q⟫ ≤ -(δ/r) * ‖Q‖ * ‖A - Q‖
    -- 7. Combined with ‖A - Q‖ < 2δ and ‖Q‖ > r:
    --    2⟪Q, A - Q⟫ + ‖A - Q‖² ≤ 2 * (-(δ/r) * ‖Q‖ * ‖A - Q‖) + ‖A - Q‖²
    --                            = ‖A - Q‖ * (‖A - Q‖ - 2δ‖Q‖/r)
    --                            < ‖A - Q‖ * (2δ - 2δ‖Q‖/r)  [since ‖A - Q‖ < 2δ]
    --                            = 2δ * ‖A - Q‖ * (1 - ‖Q‖/r)
    --                            < 0  [since ‖Q‖ > r]
    --
    -- The remaining challenge is formalizing step 6: that A - Q being in the
    -- interior direction means it can be bounded by the angle condition on edges.
    sorry
  have h_nonneg_A : 0 ≤ ‖A‖ := norm_nonneg A
  have h_nonneg_Q : 0 ≤ ‖Q‖ := norm_nonneg Q
  nlinarith [sq_nonneg ‖A‖, sq_nonneg ‖Q‖]
