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

/--
Rotation preserves convexity
-/
theorem rotation_preserves_convex {S : Set ℝ³} (s_convex : Convex ℝ S) (rot : SO3) :
    Convex ℝ (rot.1.toEuclideanLin '' S) := by
  apply Convex.linear_image s_convex

def inject_xy (v : ℝ²) : ℝ³ := !₂[v 0, v 1, 0]

/--
Injecting ℝ² into ℝ³ commutes as expected with projection and sum
-/
theorem proj_offset_commute (t : ℝ²) (v : ℝ³) : (proj_xy v) + t = proj_xy (v + inject_xy t) := by
 ext i; fin_cases i <;> simp [proj_xy, inject_xy]

theorem proj_xyL_offset_commute (t : ℝ²) (v : ℝ³) :
    proj_xyL v + t = proj_xyL (v + inject_xy t) := by
  simpa [proj_xy_eq_proj_xyL] using proj_offset_commute t v

end
