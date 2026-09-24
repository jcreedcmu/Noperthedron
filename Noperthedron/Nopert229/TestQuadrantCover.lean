import Noperthedron.BalancedSupport.AxisFree

open scoped RealInnerProductSpace

/-- A single box covering lemma: given linear bounds on a . k1, a . k2, and a . u0,
    an affine combination v = c1 • k1 + c2 • k2 + c0 • u0 achieves inner product
    ≥ c_core whenever the worst-case corner evaluation exceeds c_core. -/
theorem box_axis_cover
    (u0 k1 k2 v : ℝ³)
    (c1 c2 c0 : ℝ)
    (x_min x_max y_min y_max c_cone c_core : ℝ)
    (hv : v = c1 • k1 + c2 • k2 + c0 • u0)
    (h_corner : c_core ≤
      (if 0 ≤ c1 then c1 * x_min else c1 * x_max) +
      (if 0 ≤ c2 then c2 * y_min else c2 * y_max) +
      c0 * c_cone)
    {a : ℝ³}
    (hx_min : x_min ≤ inner ℝ a k1)
    (hx_max : inner ℝ a k1 ≤ x_max)
    (hy_min : y_min ≤ inner ℝ a k2)
    (hy_max : inner ℝ a k2 ≤ y_max)
    (ha_u : c_cone ≤ inner ℝ a u0)
    (hc0_nonneg : 0 ≤ c0) :
    c_core ≤ inner ℝ a v := by
  have hav : inner ℝ a v = c1 * inner ℝ a k1 + c2 * inner ℝ a k2 + c0 * inner ℝ a u0 := by
    rw [hv]
    simp only [inner_add_right, inner_smul_right]
  have h1 : (if 0 ≤ c1 then c1 * x_min else c1 * x_max) ≤ c1 * inner ℝ a k1 := by
    split_ifs with hc1
    · exact mul_le_mul_of_nonneg_left hx_min hc1
    · have hc1' : 0 ≤ -c1 := by linarith
      have h := mul_le_mul_of_nonneg_left hx_max hc1'
      linarith
  have h2 : (if 0 ≤ c2 then c2 * y_min else c2 * y_max) ≤ c2 * inner ℝ a k2 := by
    split_ifs with hc2
    · exact mul_le_mul_of_nonneg_left hy_min hc2
    · have hc2' : 0 ≤ -c2 := by linarith
      have h := mul_le_mul_of_nonneg_left hy_max hc2'
      linarith
  have h3 : c0 * c_cone ≤ c0 * inner ℝ a u0 := mul_le_mul_of_nonneg_left ha_u hc0_nonneg
  linarith
