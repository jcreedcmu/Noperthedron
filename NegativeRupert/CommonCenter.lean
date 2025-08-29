import Rupert.Basic
import Rupert.Set
import NegativeRupert.RotRupert

open scoped Matrix

def PointSym {n : ℕ} (A : Set (Fin n → ℝ)) : Prop :=
 ∀ x ∈ A, -x ∈ A

lemma segment_lemma (k : ℝ) (a v : ℝ²) : k • a + k • v + k • (a - v) = (k * 2) • a := by
 rw [smul_sub]
 calc (k • a + k • v) + (k • a - k • v)
 _ = k • a + (k • v + (k • a - k • v)) := by rw [add_assoc]
 _ = k • a + (k • v + ((-(k • v)) + k • a)) := by nth_rw 5 [add_comm]; rfl
 _ = k • a + ((k • v + (-(k • v))) + k • a) := by nth_rw 1 [add_assoc]
 _ = k • a + k • a := by rw [add_neg_cancel, zero_add]
 _ = (k * 2) • a := by rw [← add_smul, ← mul_two]

/--
Suppose A and B are both pointsymmetric subsets of ℝ². Suppose B is convex.
If some translate of A is contained in B, then A is contained in B.
-/
theorem common_center {A B : Set ℝ²} (psa : PointSym A) (psb : PointSym B)
    (b_convex : Convex ℝ B)
    (v : ℝ²) (hin : (· + v) '' A ⊆ B) : A ⊆ B := by
  intro a ha
  have h1 : a + v ∈ B := by
    grind only [= Set.mem_image, = Set.subset_def]
  have h2 : a - v ∈ B := by
    have han : -a ∈ A := psa a ha
    have hnav : -a + v ∈ B := by grind only [= Set.mem_image, = Set.subset_def]
    have hnn : -(-a + v) ∈ B := psb (-a + v) hnav
    have e : -(-a + v) = a - v := by grind only
    rw [e] at hnn
    exact hnn
  have segment_sub_b := convex_iff_segment_subset.mp b_convex h1 h2
  have a_in_segment : a ∈ segment ℝ (a + v) (a - v) := by
    unfold segment
    simp only [smul_add, exists_and_left, Set.mem_setOf_eq]
    refine ⟨ 1/2, ?_, 1/2, ?_, ?_, ?_ ⟩
    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    · grind
    · rw [segment_lemma (1/2) a v]
      norm_num
  exact segment_sub_b a_in_segment

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
    Convex ℝ (proj_xy '' S) := by
  sorry

/--
Rotation preserves convexity
-/
theorem rotation_pres_convex {S : Set ℝ³} (s_convex : Convex ℝ S) (rot : SO3) :
    Convex ℝ ((fun x => rot.1 *ᵥ x) '' S) := by
  sorry

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
If a set is point symmetric and convex, then it being rupert implies
being purely rotationally rupert.
-/
theorem rupert_implies_rot_rupert {S : Set ℝ³} (s_sym : PointSym S) (s_convex : Convex ℝ S)
    (r : IsRupertSet S) : IsRotRupertSet S := by
  unfold IsRupertSet IsRupertPair at r
  obtain ⟨inn, inn_so3, off, out, out_so3, shadow_sub⟩ := r
  let shift := translationHomeo off
  let pose := Pose.mk ⟨inn, inn_so3⟩ ⟨out, out_so3⟩ 0
  let pose' := Pose.mk ⟨inn, inn_so3⟩ ⟨out, out_so3⟩ off
  use pose
  refine ⟨rfl, ?_⟩

  let inner_shadow' := pose'.innerShadow S

  have inner_shadow'_eq : shift '' closure (pose.innerShadow S) = closure inner_shadow' := by
    rw [Homeomorph.image_closure shift]
    refine congrArg closure ?_
    change _ '' ((fun p => 0 + proj_xy (pose.innerRot *ᵥ p)) '' S) = _
    rw [← Set.image_comp]
    change (fun p ↦ (0 + proj_xy _) + off) '' _ = _
    conv => lhs; lhs; intro p; rw [zero_add, add_comm]
    rfl

  change closure inner_shadow' ⊆ interior (pose.outerShadow S) at shadow_sub
  refine common_center ?_ ?_ ?_ off ?_
  · refine closure_pres_point_sym ?_
    change PointSym ((fun z => 0 + proj_xy (inn *ᵥ z)) '' S)
    conv => rhs; lhs; intro z; rw [zero_add]
    change PointSym ((proj_xy ∘ (fun z => inn *ᵥ z)) '' S)
    rw [Set.image_comp]
    exact proj_pres_point_sym (rotation_pres_point_sym s_sym ⟨inn, inn_so3⟩)
  · refine interior_pres_point_sym ?_
    change PointSym ((proj_xy ∘ (fun z => out *ᵥ z)) '' S)
    rw [Set.image_comp]
    exact proj_pres_point_sym (rotation_pres_point_sym s_sym ⟨out, out_so3⟩)
  · refine Convex.interior ?_
    change Convex ℝ ((proj_xy ∘ (out *ᵥ ·)) '' S)
    rw [Set.image_comp]
    exact proj_pres_convex (rotation_pres_convex s_convex ⟨out, out_so3⟩)
  · change shift '' _ ⊆ _; rw [inner_shadow'_eq]; exact shadow_sub
