import Noperthedron.Rupert.Basic
import Noperthedron.Rupert.Equivalences.Util

open scoped Matrix

/--
Translation as a homeomorphism ℝⁿ → ℝⁿ
-/
noncomputable def translationHomeo {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    Homeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
{ toFun := fun x ↦ x + v,
  invFun := fun x ↦ x - v,
  left_inv := leftInverse_sub_add_left v
  right_inv := by intro; simp,
  continuous_toFun := continuous_add_right v
  continuous_invFun := continuous_sub_right v
}

/--
Translation AffineEquiv ℝⁿ → ℝⁿ
-/
noncomputable def translationAffineEquiv {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
{ toFun x := x + v,
  invFun x := x - v,
  linear := by rfl,
  map_vadd' m x := add_assoc x m v,
  right_inv := by grind only [= Function.RightInverse.eq_1, = Function.LeftInverse.eq_1],
  left_inv := leftInverse_sub_add_left v
  }

/--
Projection preserves convexity
-/
theorem proj_preserves_convex {S : Set ℝ³} (s_convex : Convex ℝ S) :
    Convex ℝ (proj_xy '' S) :=
  Convex.linear_image s_convex proj_xy_linear

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
