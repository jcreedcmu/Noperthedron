import Noperthedron.Rupert.Basic
import Noperthedron.Rupert.Equivalences.Util

open scoped Matrix

def PointSym {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
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
    · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, PiLp.neg_apply,
        neg_inj, ←he]
      rfl
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, PiLp.neg_apply, neg_inj, ←he]
      rfl

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
  left_inv := by grind only [= Function.LeftInverse.eq_1],
  }

/--
Pointsymmetric flip as a homeomorphism
-/
def pointSymHomeo {n : ℕ} : Homeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
{ toFun := fun x ↦ -x,
  invFun := fun x ↦ -x,
  left_inv := by intro; simp,
  right_inv := by intro; simp,
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg
}

/--
Pointsymmetric flip as a linear map
-/
noncomputable
def pointSymLinEquiv {n : ℕ} : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
{ toFun := fun x ↦ -x,
  invFun := fun x ↦ -x,
  left_inv := leftInverse_neg _
  right_inv := rightInverse_neg _
  map_add' := neg_add
  map_smul' := by intro m x;  simp only [smul_neg, RingHom.id_apply]
}

/--
Topological closure preserves the property of being pointsymmetric.
-/
theorem closure_pres_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
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
theorem interior_pres_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
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
    PointSym (rot.1.toEuclideanLin  '' S) := by
  intro a ⟨y, hy, e⟩
  aesop

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
    Convex ℝ (rot.1.toEuclideanLin '' S) := by
  apply Convex.linear_image s_convex

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


def inject_xy (v : ℝ²) : ℝ³ := !₂[v 0, v 1, 0]

/--
Injecting ℝ² into ℝ³ commutes as expected with projection and sum
-/
theorem proj_offset_commute (t : ℝ²) (v : ℝ³) : (proj_xy v) + t = proj_xy (v + inject_xy t) := by
 ext i; fin_cases i <;> simp [proj_xy, inject_xy]
