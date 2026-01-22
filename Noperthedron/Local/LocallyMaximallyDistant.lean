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
If all other vertices Pᵢ satisfy ⟪Q, Q - Pᵢ⟫ > 0 (i.e., they're in a strict half-space),
then Q cannot be in the interior of convexHull P.

Proof: The condition implies P ⊆ {x : ⟪Q, x⟫ ≤ ‖Q‖²}, so convexHull P ⊆ {x : ⟪Q, x⟫ ≤ ‖Q‖²}.
But Q is on the boundary of this half-space, so Q ∉ interior(convexHull P).
-/
private lemma angle_condition_implies_not_interior {P : Finset Euc(2)} {Q : Euc(2)}
    (_hQ : Q ∈ P) (hQ_ne_zero : Q ≠ 0)
    (h_angle : ∀ Pᵢ ∈ P, Pᵢ ≠ Q → ⟪Q, Q - Pᵢ⟫ > 0) :
    Q ∉ interior (convexHull ℝ (P : Set Euc(2))) := by
  intro hQ_int
  -- From h_angle: all Pᵢ ≠ Q satisfy ⟪Q, Pᵢ⟫ < ‖Q‖²
  have h_halfspace : ∀ Pᵢ ∈ P, ⟪Q, Pᵢ⟫ ≤ ‖Q‖^2 := by
    intro Pᵢ hPᵢ
    by_cases heq : Pᵢ = Q
    · simp [heq]
    · have h1 := h_angle Pᵢ hPᵢ heq
      simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h1
      linarith
  -- convexHull P ⊆ {x : ⟪Q, x⟫ ≤ ‖Q‖²}
  have h_hull_in_halfspace : convexHull ℝ (P : Set Euc(2)) ⊆ {x : Euc(2) | ⟪Q, x⟫ ≤ ‖Q‖^2} := by
    apply convexHull_min
    · intro x hx
      simp only [Set.mem_setOf_eq]
      exact h_halfspace x hx
    · -- The half-space {x : ⟪Q, x⟫ ≤ c} is convex
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      calc ⟪Q, a • x + b • y⟫ = a * ⟪Q, x⟫ + b * ⟪Q, y⟫ := by
              simp [inner_add_right, inner_smul_right]
        _ ≤ a * ‖Q‖^2 + b * ‖Q‖^2 := by nlinarith
        _ = (a + b) * ‖Q‖^2 := by ring
        _ = ‖Q‖^2 := by rw [hab, one_mul]
  -- Q ∈ interior(convexHull P) means there's an open set U with Q ∈ U ⊆ convexHull P
  rw [mem_interior] at hQ_int
  obtain ⟨U, hU_sub, hU_open, hQ_in_U⟩ := hQ_int
  -- Since U is open and Q ∈ U, there exists ε > 0 such that B(Q, ε) ⊆ U
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨ε, hε_pos, hball_sub_U⟩ := hU_open Q hQ_in_U
  -- Consider Q + (ε/2) * (Q / ‖Q‖) - this is in B(Q, ε) ⊆ U ⊆ convexHull P
  have hQ_pos : 0 < ‖Q‖ := norm_pos_iff.mpr hQ_ne_zero
  let v := (ε / (2 * ‖Q‖)) • Q  -- direction scaled to have norm ε/2
  have hv_norm : ‖v‖ = ε / 2 := by
    simp only [v, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ε / (2 * ‖Q‖))]
    field_simp
  have hQv_in_ball : Q + v ∈ Metric.ball Q ε := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hv_norm]
    linarith
  have hQv_in_hull : Q + v ∈ convexHull ℝ (P : Set Euc(2)) :=
    hU_sub (hball_sub_U hQv_in_ball)
  -- But ⟪Q, Q + v⟫ > ‖Q‖², contradicting Q + v ∈ convexHull P ⊆ {x : ⟪Q, x⟫ ≤ ‖Q‖²}
  have hQv_inner : ⟪Q, Q + v⟫ = ‖Q‖^2 + (ε / 2) * ‖Q‖ := by
    simp only [v, inner_add_right, inner_smul_right]
    have h_inner_Q : ⟪Q, Q⟫ = ‖Q‖^2 := inner_self_eq_norm_sq_to_K Q
    rw [h_inner_Q]
    field_simp
  have hQv_gt : ⟪Q, Q + v⟫ > ‖Q‖^2 := by
    rw [hQv_inner]
    have : (ε / 2) * ‖Q‖ > 0 := by positivity
    linarith
  have hQv_le : ⟪Q, Q + v⟫ ≤ ‖Q‖^2 := h_hull_in_halfspace hQv_in_hull
  linarith

/--
Key algebraic identity: ‖A‖² - ‖Q‖² = 2⟪Q, A - Q⟫ + ‖A - Q‖²
-/
private lemma norm_sq_diff_eq {A Q : Euc(2)} :
    ‖A‖^2 - ‖Q‖^2 = 2 * ⟪Q, A - Q⟫ + ‖A - Q‖^2 := by
  have h := norm_add_sq_real Q (A - Q)
  simp only [add_sub_cancel] at h
  linarith

/--
For A in convexHull P, A can be written as a convex combination of vertices,
and ⟪Q, A - Q⟫ = Σ wᵢ ⟪Q, Pᵢ - Q⟫.
-/
private lemma inner_convex_combination {P : Finset Euc(2)} {Q A : Euc(2)}
    (hA : A ∈ convexHull ℝ (P : Set Euc(2))) :
    ∃ w : Euc(2) → ℝ, (∀ y ∈ P, 0 ≤ w y) ∧ (∑ y ∈ P, w y = 1) ∧
      (∑ y ∈ P, w y • y = A) ∧
      ⟪Q, A - Q⟫ = ∑ y ∈ P, w y * ⟪Q, y - Q⟫ := by
  rw [Finset.mem_convexHull'] at hA
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ := hA
  refine ⟨w, hw_nonneg, hw_sum, hw_eq, ?_⟩
  calc ⟪Q, A - Q⟫ = ⟪Q, ∑ y ∈ P, w y • y - Q⟫ := by rw [hw_eq]
    _ = ⟪Q, ∑ y ∈ P, w y • y - (∑ y ∈ P, w y) • Q⟫ := by rw [hw_sum, one_smul]
    _ = ⟪Q, ∑ y ∈ P, w y • y - ∑ y ∈ P, w y • Q⟫ := by rw [Finset.sum_smul]
    _ = ⟪Q, ∑ y ∈ P, (w y • y - w y • Q)⟫ := by rw [← Finset.sum_sub_distrib]
    _ = ⟪Q, ∑ y ∈ P, w y • (y - Q)⟫ := by simp_rw [← smul_sub]
    _ = ∑ y ∈ P, ⟪Q, w y • (y - Q)⟫ := inner_sum P (fun y ↦ w y • (y - Q)) Q
    _ = ∑ y ∈ P, w y * ⟪Q, y - Q⟫ := by simp_rw [real_inner_smul_right]

/--
If the angle condition holds and Q ≠ 0, then ⟪Q, Pᵢ - Q⟫ is bounded above by a negative quantity.
-/
private lemma inner_toward_vertex_neg {Q : Euc(2)} {δ r : ℝ}
    (hr : 0 < r) (hrQ : r < ‖Q‖) (Pᵢ : Euc(2)) (hne : Pᵢ ≠ Q)
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
  -- A is in the interior, so it's in the convex hull
  have hA_hull : A ∈ convexHull ℝ (P : Set Euc(2)) := interior_subset hA_interior
  -- Get convex combination representation and the inner product identity
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq, hw_inner⟩ := inner_convex_combination hA_hull
  -- Key bound: ⟪Q, A - Q⟫ ≤ -(δ/r) * ‖Q‖ * ‖A - Q‖
  -- First bound the inner product using angle conditions on each vertex
  have h_inner_bound : ⟪Q, A - Q⟫ ≤ -(δ / r) * ‖Q‖ * ∑ y ∈ P, w y * ‖y - Q‖ := by
    rw [hw_inner]
    -- Split sum at Q: the Q term vanishes
    have h_sum_split : ∑ y ∈ P, w y * ⟪Q, y - Q⟫ =
        w Q * ⟪Q, Q - Q⟫ + ∑ y ∈ P.erase Q, w y * ⟪Q, y - Q⟫ := by
      rw [← Finset.add_sum_erase P (fun y ↦ w y * ⟪Q, y - Q⟫) hQ]
    rw [h_sum_split]
    simp only [sub_self, inner_zero_right, mul_zero, zero_add]
    -- For y ≠ Q, use the angle bound
    have h_term_bound : ∀ y ∈ P.erase Q, w y * ⟪Q, y - Q⟫ ≤ w y * (-(δ / r) * ‖Q‖ * ‖y - Q‖) := by
      intro y hy
      have hy_mem : y ∈ P := Finset.mem_of_mem_erase hy
      have hy_ne : y ≠ Q := Finset.ne_of_mem_erase hy
      have h_vertex := inner_toward_vertex_neg hr hrQ y hy_ne (hle y hy_mem hy_ne)
      have hw_y_nonneg : 0 ≤ w y := hw_nonneg y hy_mem
      rw [norm_sub_rev Q y] at h_vertex
      exact mul_le_mul_of_nonneg_left h_vertex hw_y_nonneg
    -- Factor out the constant from the sum
    have h_sum_factor : ∑ y ∈ P.erase Q, w y * (-(δ / r) * ‖Q‖ * ‖y - Q‖) =
        -(δ / r) * ‖Q‖ * ∑ y ∈ P.erase Q, w y * ‖y - Q‖ := by
      rw [Finset.mul_sum]; congr 1; ext y; ring
    -- Extend back to sum over P (Q term is 0)
    have h_sum_extend : ∑ y ∈ P.erase Q, w y * ‖y - Q‖ = ∑ y ∈ P, w y * ‖y - Q‖ := by
      rw [← Finset.add_sum_erase P (fun y ↦ w y * ‖y - Q‖) hQ]
      simp only [sub_self, norm_zero, mul_zero, zero_add]
    calc ∑ y ∈ P.erase Q, w y * ⟪Q, y - Q⟫
        ≤ ∑ y ∈ P.erase Q, w y * (-(δ / r) * ‖Q‖ * ‖y - Q‖) := Finset.sum_le_sum h_term_bound
      _ = -(δ / r) * ‖Q‖ * ∑ y ∈ P.erase Q, w y * ‖y - Q‖ := h_sum_factor
      _ = -(δ / r) * ‖Q‖ * ∑ y ∈ P, w y * ‖y - Q‖ := by rw [h_sum_extend]
  -- Triangle inequality for convex combination: ‖A - Q‖ ≤ ∑ wᵢ ‖yᵢ - Q‖
  have h_norm_bound : ‖A - Q‖ ≤ ∑ y ∈ P, w y * ‖y - Q‖ := by
    -- A - Q = ∑ wᵢ (yᵢ - Q) because A = ∑ wᵢ yᵢ and ∑ wᵢ = 1
    have hAQ_eq : A - Q = ∑ y ∈ P, w y • (y - Q) := by
      calc A - Q = ∑ y ∈ P, w y • y - Q := by rw [hw_eq]
        _ = ∑ y ∈ P, w y • y - (∑ y ∈ P, w y) • Q := by rw [hw_sum, one_smul]
        _ = ∑ y ∈ P, w y • y - ∑ y ∈ P, w y • Q := by rw [Finset.sum_smul]
        _ = ∑ y ∈ P, (w y • y - w y • Q) := by rw [← Finset.sum_sub_distrib]
        _ = ∑ y ∈ P, w y • (y - Q) := by simp_rw [← smul_sub]
    rw [hAQ_eq]
    calc ‖∑ y ∈ P, w y • (y - Q)‖
        ≤ ∑ y ∈ P, ‖w y • (y - Q)‖ := norm_sum_le P (fun y ↦ w y • (y - Q))
      _ = ∑ y ∈ P, |w y| * ‖y - Q‖ := by simp_rw [norm_smul, Real.norm_eq_abs]
      _ = ∑ y ∈ P, w y * ‖y - Q‖ := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [abs_of_nonneg (hw_nonneg y hy)]
  -- Combine: ⟪Q, A - Q⟫ ≤ -(δ/r) * ‖Q‖ * ‖A - Q‖
  -- First we need δ > 0 (since ‖Q - Q_‖ < δ and norms are ≥ 0)
  have hδ_pos : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hQ_
  have h_coeff_neg : -(δ / r) * ‖Q‖ ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith [div_pos hδ_pos hr]
    · exact le_of_lt hQ_pos
  have h_inner_final : ⟪Q, A - Q⟫ ≤ -(δ / r) * ‖Q‖ * ‖A - Q‖ := by
    calc ⟪Q, A - Q⟫ ≤ -(δ / r) * ‖Q‖ * ∑ y ∈ P, w y * ‖y - Q‖ := h_inner_bound
      _ ≤ -(δ / r) * ‖Q‖ * ‖A - Q‖ := mul_le_mul_of_nonpos_left h_norm_bound h_coeff_neg
  -- Show ‖A‖² < ‖Q‖² by showing the difference is negative
  have h_sq_diff : ‖A‖^2 - ‖Q‖^2 < 0 := by
    rw [norm_sq_diff_eq]
    -- 2⟪Q, A - Q⟫ + ‖A - Q‖² < 0
    -- We have: ⟪Q, A - Q⟫ ≤ -(δ/r) * ‖Q‖ * ‖A - Q‖
    -- So: 2⟪Q, A - Q⟫ + ‖A - Q‖² ≤ -2(δ/r)‖Q‖‖A - Q‖ + ‖A - Q‖²
    --                              = ‖A - Q‖ * (‖A - Q‖ - 2δ‖Q‖/r)
    -- Since ‖A - Q‖ < 2δ and ‖Q‖ > r, we have ‖A - Q‖ - 2δ‖Q‖/r < 0
    have h2 : 2 * δ * ‖Q‖ / r > 2 * δ := by
      rw [gt_iff_lt, lt_div_iff₀ hr]
      nlinarith [hδ_pos, hrQ]
    have h_factor : ‖A - Q‖ - 2 * δ * ‖Q‖ / r < 0 := by linarith
    -- Now: 2⟪Q, A - Q⟫ + ‖A - Q‖² ≤ 2 * (-(δ/r) * ‖Q‖ * ‖A - Q‖) + ‖A - Q‖²
    --                                = ‖A - Q‖ * (‖A - Q‖ - 2δ‖Q‖/r)
    --                                < 0 since h_factor shows the second term is negative
    have h_AQ_nonneg : 0 ≤ ‖A - Q‖ := norm_nonneg _
    -- Case split on whether A = Q
    by_cases hAQ_zero : ‖A - Q‖ = 0
    · -- If A = Q, then A is a vertex in the interior of the convex hull.
      -- This is impossible: vertices of a finite set are extreme points of the hull,
      -- and extreme points cannot be interior points.
      have hAQ_eq : A = Q := by
        rw [← sub_eq_zero]
        exact (norm_eq_zero (E := Euc(2))).mp hAQ_zero
      rw [hAQ_eq] at hA_interior
      -- The angle condition implies ⟪Q, Q - Pᵢ⟫ > 0 for all Pᵢ ≠ Q
      have h_angle : ∀ Pᵢ ∈ P, Pᵢ ≠ Q → ⟪Q, Q - Pᵢ⟫ > 0 := by
        intro Pᵢ hPᵢ hne
        have h := hle Pᵢ hPᵢ hne
        have hQPᵢ_pos : 0 < ‖Q - Pᵢ‖ := norm_sub_pos_iff.mpr hne.symm
        have hdenom_pos : 0 < ‖Q‖ * ‖Q - Pᵢ‖ := mul_pos hQ_pos hQPᵢ_pos
        have h' := (le_div_iff₀ hdenom_pos).mp h
        have hδr_pos : 0 < δ / r := div_pos hδ_pos hr
        calc ⟪Q, Q - Pᵢ⟫ ≥ δ / r * (‖Q‖ * ‖Q - Pᵢ‖) := h'
          _ > 0 := by positivity
      have hQ_ne_zero : Q ≠ 0 := norm_pos_iff.mp hQ_pos
      exact absurd hA_interior (angle_condition_implies_not_interior hQ hQ_ne_zero h_angle)
    · -- If ‖A - Q‖ > 0
      have h_AQ_pos : 0 < ‖A - Q‖ := lt_of_le_of_ne h_AQ_nonneg (Ne.symm hAQ_zero)
      -- Use the bound
      have h_bound : 2 * ⟪Q, A - Q⟫ ≤ 2 * (-(δ / r) * ‖Q‖ * ‖A - Q‖) := by linarith [h_inner_final]
      have h_rhs : 2 * (-(δ / r) * ‖Q‖ * ‖A - Q‖) + ‖A - Q‖^2 =
          ‖A - Q‖ * (‖A - Q‖ - 2 * δ * ‖Q‖ / r) := by ring
      calc 2 * ⟪Q, A - Q⟫ + ‖A - Q‖^2 ≤ 2 * (-(δ / r) * ‖Q‖ * ‖A - Q‖) + ‖A - Q‖^2 := by linarith
        _ = ‖A - Q‖ * (‖A - Q‖ - 2 * δ * ‖Q‖ / r) := h_rhs
        _ < 0 := mul_neg_of_pos_of_neg h_AQ_pos h_factor
  -- From ‖A‖² < ‖Q‖², conclude ‖A‖ < ‖Q‖
  have h_nonneg_A : 0 ≤ ‖A‖ := norm_nonneg A
  have h_nonneg_Q : 0 ≤ ‖Q‖ := norm_nonneg Q
  nlinarith [sq_nonneg ‖A‖, sq_nonneg ‖Q‖, sq_nonneg (‖A‖ - ‖Q‖), sq_nonneg (‖A‖ + ‖Q‖)]
