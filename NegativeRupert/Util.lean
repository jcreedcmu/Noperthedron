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
    · simp only [Fin.isValue, Fin.zero_eta, PiLp.toLp_apply, Matrix.cons_val_zero, Pi.neg_apply,
      neg_inj]
      exact congrFun he 0
    · simp only [Fin.isValue, Fin.mk_one, PiLp.toLp_apply, Matrix.cons_val_one,
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
Pointsymmetric flip as a linear map
-/
noncomputable
def pointSymLinEquiv {n : ℕ} : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
{ toFun := fun x ↦ -x,
  invFun := fun x ↦ -x,
  left_inv := by intro; simp,
  right_inv := by intro; simp,
  map_add' := by intro x y; exact neg_add x y
  map_smul' := by intro m x;  simp only [smul_neg, RingHom.id_apply]
}

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

/--
If S is a pointsymmetric set, then the flip of S is equal to S.
-/
lemma pointsym_imp_flip_pres {S : Set ℝ³} (s_psym : PointSym S) :
    S = pointSymLinEquiv '' S := by
  ext x
  constructor
  · intro hx; rw [Set.mem_image]; use -x, s_psym _ hx; simp [pointSymLinEquiv]
  · intro hx; rw [Set.mem_image] at hx;
    obtain ⟨y, hy, e⟩ := hx; rw [← e];
    exact s_psym _ hy

/--
Taking the convex hull preserves point symmetry.
-/
lemma hull_pres_pointsym {S : Set ℝ³} (s_psym : PointSym S) : PointSym (convexHull ℝ S) := by
  intro a ha
  apply mem_convexHull_iff.mpr
  intro T ht hc

  let T' : Set ℝ³ := pointSymLinEquiv '' T

  have ht' : S ⊆ T' := by
    rw [pointsym_imp_flip_pres s_psym]
    exact (Equiv.image_subset pointSymLinEquiv.toEquiv S T).mpr ht

  have hc' : Convex ℝ T' := Convex.linear_image hc pointSymLinEquiv.toLinearMap
  have a_in_T' := mem_convexHull_iff.mp ha T' ht' hc'
  rw [Set.mem_image] at a_in_T'; obtain ⟨y, hy, e⟩ := a_in_T'; rw [← e]
  simp only [pointSymLinEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, neg_neg]
  exact hy


def inject_xy (v : ℝ²) : ℝ³ := fun i => match i with
 | 0 => v 0
 | 1 => v 1
 | 2 => 0

/--
Injecting ℝ² into ℝ³ commutes as expected with projection and sum
-/
theorem proj_offset_commute (t : ℝ²) (v : ℝ³) : (proj_xy v) + t = proj_xy (v + inject_xy t) := by
 ext i; fin_cases i <;> simp [proj_xy, inject_xy]
