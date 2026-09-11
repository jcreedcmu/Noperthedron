module

public import Noperthedron.Basic

@[expose] public section


open scoped Matrix

/--
Projection preserves convexity
-/
theorem proj_preserves_convex {S : Set ℝ³} (s_convex : Convex ℝ S) :
    Convex ℝ (proj_xy '' S) := by
  rw [proj_xy_eq_proj_xyL]
  exact Convex.linear_image s_convex (proj_xyL : ℝ³ →L[ℝ] ℝ²).toLinearMap

end
