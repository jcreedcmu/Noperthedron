module

public import Noperthedron.Basic

@[expose] public section


def PointSym {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
 ∀ x ∈ A, -x ∈ A

theorem continuousLinearMap_preserves_point_sym {m n : ℕ} (f : Euc(n) →L[ℝ] Euc(m))
    {S : Set (Euc(n))} (s_sym : PointSym S) : PointSym (f '' S) := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨-y, s_sym y hy, ?_⟩
  rw [f.map_neg]

lemma neg_image_eq_if_pointsym {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (hA : PointSym A) :
    (-·) '' A = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hA y hy
  · intro hx
    refine ⟨-x, hA x hx, ?_⟩
    simp

lemma pointsym_of_neg_image_eq {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : (-·) '' S = S) : PointSym S := by
  intro x hx
  rw [← hS]
  exact Set.mem_image_of_mem (fun x ↦ -x) hx

/--
Topological closure preserves the property of being pointsymmetric.
-/
theorem closure_preserves_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (s_sym : PointSym S) : PointSym (closure S) := by
  apply pointsym_of_neg_image_eq
  calc
    (fun x => -x) '' closure S = closure ((fun x => -x) '' S) :=
      Homeomorph.image_closure (Homeomorph.neg _) S
    _ = closure S := by rw [neg_image_eq_if_pointsym S s_sym]

/--
Topological interior preserves the property of being pointsymmetric.
-/
theorem interior_preserves_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (s_sym : PointSym S) : PointSym (interior S) := by
  apply pointsym_of_neg_image_eq
  calc
    (fun x => -x) '' interior S = interior ((fun x => -x) '' S) :=
      Homeomorph.image_interior (Homeomorph.neg _) S
    _ = interior S := by rw [neg_image_eq_if_pointsym S s_sym]

/--
Rotation preserves the property of being pointsymmetric.
-/
theorem rotation_preserves_point_sym {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (s_sym : PointSym S) (rot : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    PointSym (rot.1.toEuclideanLin '' S) :=
  continuousLinearMap_preserves_point_sym rot.1.toEuclideanLin.toContinuousLinearMap s_sym

/--
Taking the convex hull preserves point symmetry.
-/
lemma hull_preserves_pointsym {S : Set (EuclideanSpace ℝ (Fin 3))} (s_psym : PointSym S) :
    PointSym (convexHull ℝ S) := by
  apply pointsym_of_neg_image_eq
  rw [Set.image_neg_eq_neg, ← convexHull_neg, ← Set.image_neg_eq_neg,
    neg_image_eq_if_pointsym S s_psym]

end
