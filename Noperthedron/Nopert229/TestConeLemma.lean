import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open scoped BigOperators RealInnerProductSpace

theorem inner_ge_of_cone3 (q1 q2 q3 : ℝ³) (v : ℝ³) (c : ℝ) (hc : 0 ≤ c)
    (hq1 : c * ‖q1‖ ≤ inner ℝ q1 v)
    (hq2 : c * ‖q2‖ ≤ inner ℝ q2 v)
    (hq3 : c * ‖q3‖ ≤ inner ℝ q3 v)
    {a : ℝ³} (ha_norm : ‖a‖ = 1)
    {b1 b2 b3 : ℝ} (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (ha_cone : a = b1 • q1 + b2 • q2 + b3 • q3) :
    c ≤ inner ℝ a v := by
  have hinner : inner ℝ a v = b1 * inner ℝ q1 v + b2 * inner ℝ q2 v + b3 * inner ℝ q3 v := by
    rw [ha_cone]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  have hbound : c * (b1 * ‖q1‖ + b2 * ‖q2‖ + b3 * ‖q3‖) ≤ inner ℝ a v := by
    rw [hinner]
    have h1 : c * (b1 * ‖q1‖) ≤ b1 * inner ℝ q1 v := by
      calc c * (b1 * ‖q1‖) = b1 * (c * ‖q1‖) := by ring
      _ ≤ b1 * inner ℝ q1 v := mul_le_mul_of_nonneg_left hq1 hb1
    have h2 : c * (b2 * ‖q2‖) ≤ b2 * inner ℝ q2 v := by
      calc c * (b2 * ‖q2‖) = b2 * (c * ‖q2‖) := by ring
      _ ≤ b2 * inner ℝ q2 v := mul_le_mul_of_nonneg_left hq2 hb2
    have h3 : c * (b3 * ‖q3‖) ≤ b3 * inner ℝ q3 v := by
      calc c * (b3 * ‖q3‖) = b3 * (c * ‖q3‖) := by ring
      _ ≤ b3 * inner ℝ q3 v := mul_le_mul_of_nonneg_left hq3 hb3
    calc c * (b1 * ‖q1‖ + b2 * ‖q2‖ + b3 * ‖q3‖)
      = c * (b1 * ‖q1‖) + c * (b2 * ‖q2‖) + c * (b3 * ‖q3‖) := by ring
      _ ≤ b1 * inner ℝ q1 v + b2 * inner ℝ q2 v + b3 * inner ℝ q3 v := by linarith
  have hnorm : ‖a‖ ≤ b1 * ‖q1‖ + b2 * ‖q2‖ + b3 * ‖q3‖ := by
    rw [ha_cone]
    calc ‖b1 • q1 + b2 • q2 + b3 • q3‖
      ≤ ‖b1 • q1 + b2 • q2‖ + ‖b3 • q3‖ := norm_add_le _ _
      _ ≤ ‖b1 • q1‖ + ‖b2 • q2‖ + ‖b3 • q3‖ := by
        have := norm_add_le (b1 • q1) (b2 • q2); linarith
      _ = |b1| * ‖q1‖ + |b2| * ‖q2‖ + |b3| * ‖q3‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ = b1 * ‖q1‖ + b2 * ‖q2‖ + b3 * ‖q3‖ := by
        rw [abs_of_nonneg hb1, abs_of_nonneg hb2, abs_of_nonneg hb3]
  have hcnorm : c * ‖a‖ ≤ c * (b1 * ‖q1‖ + b2 * ‖q2‖ + b3 * ‖q3‖) :=
    mul_le_mul_of_nonneg_left hnorm hc
  rw [ha_norm, mul_one] at hcnorm
  exact hcnorm.trans hbound
