import Noperthedron.Rupert.Basic

def PointSym {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
 ∀ x ∈ A, -x ∈ A

/--
Projection preserves the property of being pointsymmetric.
-/
theorem proj_preserves_point_sym {S : Set ℝ³} (s_sym : PointSym S) : PointSym (proj_xy '' S) := by
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
Pointsymmetric flip as a homeomorphism
-/
def pointSymHomeo {n : ℕ} : Homeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
{ toFun := fun x ↦ -x,
  invFun := fun x ↦ -x,
  left_inv := leftInverse_neg _
  right_inv := rightInverse_neg _
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
theorem closure_preserves_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
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
theorem interior_preserves_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
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
theorem rotation_preserves_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (s_sym : PointSym S) (rot : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    PointSym (rot.1.toEuclideanLin '' S) := by
  intro a ⟨y, hy, e⟩
  aesop

/--
If S is a pointsymmetric set, then the flip of S is equal to S.
-/
lemma pointsym_imp_flip_pres {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (s_psym : PointSym S) :
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
lemma hull_preserves_pointsym {S : Set (EuclideanSpace ℝ (Fin 3))} (s_psym : PointSym S) :
    PointSym (convexHull ℝ S) := by
  intro a ha
  apply mem_convexHull_iff.mpr
  intro T ht hc

  let T' : Set ℝ³ := pointSymLinEquiv '' T

  have ht' : S ⊆ T' := by
    rw [pointsym_imp_flip_pres s_psym]
    exact Set.image_mono ht

  have hc' : Convex ℝ T' := Convex.linear_image hc pointSymLinEquiv.toLinearMap
  have a_in_T' := mem_convexHull_iff.mp ha T' ht' hc'
  rw [Set.mem_image] at a_in_T'; obtain ⟨y, hy, e⟩ := a_in_T'; rw [← e]
  simp only [pointSymLinEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, neg_neg]
  exact hy

lemma neg_image_eq_if_pointsym {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (hA : PointSym A) :
    (-·) '' A = A := by
  ext x
  constructor
  · intro hx
    simp only [Set.image_neg_eq_neg] at hx
    have := hA (-x) hx
    simpa using this
  · intro hx
    simp only [Set.image_neg_eq_neg, Set.mem_neg]
    refine hA x hx
