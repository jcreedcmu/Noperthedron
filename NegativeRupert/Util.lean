import Rupert.Basic
import Rupert.Equivalences.Util

open scoped Matrix

def PointSym {n : ℕ} (A : Set (Fin n → ℝ)) : Prop :=
 ∀ x ∈ A, -x ∈ A

/--
Projection preserves the property of being pointsymmetric.
-/
theorem proj_pres_point_sym {S : Set ℝ³} (s_sym : PointSym S) : PointSym (proj_xy '' S) := by
  intro a ⟨b, hb, he⟩
  use -b
  refine ⟨?_, ?_⟩
  · exact s_sym b hb
  · simp [proj_xy] ; ext i; fin_cases i;
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.neg_apply, neg_inj]
      exact congrFun he 0
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Pi.neg_apply, neg_inj]
      exact congrFun he 1

/--
Translation as a homeomorphism ℝⁿ → ℝⁿ
-/
def translationHomeo {n : ℕ} (v : Fin n → ℝ) : Homeomorph (Fin n → ℝ) (Fin n → ℝ) :=
{ toFun := fun x ↦ x + v,
  invFun := fun x ↦ x - v,
  left_inv := by intro; simp,
  right_inv := by intro; simp,
  continuous_toFun := continuous_pi fun i ↦ (continuous_apply i).add continuous_const,
  continuous_invFun := continuous_pi fun i ↦ (continuous_apply i).sub continuous_const }

/--
Translation AffineEquiv ℝⁿ → ℝⁿ
-/
def translationAffineEquiv {n : ℕ} (v : Fin n → ℝ) : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) :=
{ toFun x := x + v,
  invFun x := x - v,
  linear := by rfl,
  map_vadd' m x := add_assoc x m v,
  right_inv := by grind only [= Function.RightInverse.eq_1, = Function.LeftInverse.eq_1],
  left_inv := by grind only [= Function.LeftInverse.eq_1],
  }

/--
Pointsymmetric flip as a homeomorphism
-/
def pointSymHomeo {n : ℕ} : Homeomorph (Fin n → ℝ) (Fin n → ℝ) :=
{ toFun := fun x ↦ -x,
  invFun := fun x ↦ -x,
  left_inv := by intro; simp,
  right_inv := by intro; simp,
  continuous_toFun := continuous_pi (fun i ↦ (continuous_apply i).neg),
  continuous_invFun := continuous_pi (fun i ↦ (continuous_apply i).neg) }

/--
Topological closure preserves the property of being pointsymmetric.
-/
theorem closure_pres_point_sym {n : ℕ} {S : Set (Fin n → ℝ)}
    (s_sym : PointSym S) : PointSym (closure S) := by
  intro a ha
  have h : (fun x => -x) '' closure S = closure ((fun x => -x) '' S) :=
    Homeomorph.image_closure pointSymHomeo S
  suffices z : S = ((fun x => -x) '' S) by
    rw [z, ← h]; exact Set.mem_image_of_mem (fun x ↦ -x) ha
  ext x
  constructor
  · intro hx; use -x; exact ⟨ s_sym x hx, by simp ⟩
  · intro ⟨ y, hy, e ⟩ ; rw [← e]; exact s_sym y hy

/--
Topological interior preserves the property of being pointsymmetric.
-/
theorem interior_pres_point_sym {n : ℕ} {S : Set (Fin n → ℝ)}
    (s_sym : PointSym S) : PointSym (interior S) := by
  intro a ha
  have h : (fun x => -x) '' interior S = interior ((fun x => -x) '' S) :=
    Homeomorph.image_interior pointSymHomeo S
  suffices z : S = ((fun x => -x) '' S) by
    rw [z, ← h]; exact Set.mem_image_of_mem (fun x ↦ -x) ha
  ext x
  constructor
  · intro hx; use -x; exact ⟨ s_sym x hx, by simp ⟩
  · intro ⟨ y, hy, e ⟩ ; rw [← e]; exact s_sym y hy

/--
Rotation preserves the property of being pointsymmetric.
-/
theorem rotation_pres_point_sym {S : Set ℝ³} (s_sym : PointSym S) (rot : SO3) :
    PointSym ((fun x => rot.1 *ᵥ x) '' S) := by
  intro a ⟨y, hy, e⟩
  exact ⟨-y, s_sym y hy, (Matrix.mulVec_neg y rot.1).trans (congrArg Neg.neg e)⟩

/--
Projection preserves convexity
-/
theorem proj_pres_convex {S : Set ℝ³} (s_convex : Convex ℝ S) :
    Convex ℝ (proj_xy '' S) :=
  Convex.linear_image s_convex proj_xy_linear

/--
Rotation preserves convexity
-/
theorem rotation_pres_convex {S : Set ℝ³} (s_convex : Convex ℝ S) (rot : SO3) :
    Convex ℝ ((fun x => rot.1 *ᵥ x) '' S) := by
  refine Convex.linear_image s_convex (Matrix.mulVecLin rot.1)
