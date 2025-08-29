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

theorem proj_pres_point_sym {S : Set ℝ³} (s_sym : PointSym S) : PointSym (proj_xy '' S) := by
  sorry

theorem closure_pres_point_sym {n : ℕ} {S : Set (Fin n → ℝ)}
    (s_sym : PointSym S) : PointSym (closure S) := by
  sorry

theorem interior_pres_point_sym {n : ℕ} {S : Set (Fin n → ℝ)}
    (s_sym : PointSym S) : PointSym (interior S) := by
  sorry

theorem rotation_pres_point_sym {S : Set ℝ³} (s_sym : PointSym S) (rot : SO3) :
    PointSym ((fun x => rot.1 *ᵥ x) '' S) := by
  sorry

theorem shadow_convex {S : Set ℝ³} (s_convex : Convex ℝ S) (out : SO3) :
    Convex ℝ {x | ∃ p ∈ S, proj_xy (out *ᵥ p) = x} := by
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
  use inn, inn_so3, out, out_so3
  intro inner_shadow outer_shadow
  let inner_shadow' := {x | ∃ p ∈ S, off + proj_xy (inn.mulVec p) = x}

  have inner_shadow'_eq : shift '' closure inner_shadow = closure inner_shadow' := by
    rw [ Homeomorph.image_closure shift ]
    refine congrArg closure ?_
    unfold inner_shadow'
    have (v : ℝ²) : off + v = v + off := by rw [ add_comm ]
    have hc : (fun p => p + off) = (fun p => off + p) := by ext p; rw [add_comm]
    change (fun p => p + off) '' ((fun p => proj_xy (inn *ᵥ p)) '' S) = _
    rw [hc, ← Set.image_comp]
    rfl

  change closure inner_shadow' ⊆ interior outer_shadow at shadow_sub
  refine common_center ?_ ?_ ?_ off ?_
  · refine closure_pres_point_sym ?_
    change PointSym ((proj_xy ∘ (fun z => inn *ᵥ z)) '' S)
    rw [Set.image_comp]
    exact proj_pres_point_sym (rotation_pres_point_sym s_sym ⟨inn, inn_so3⟩)
  · refine interior_pres_point_sym ?_
    change PointSym ((proj_xy ∘ (fun z => out *ᵥ z)) '' S)
    rw [Set.image_comp]
    exact proj_pres_point_sym (rotation_pres_point_sym s_sym ⟨out, out_so3⟩)
  · refine Convex.interior ?_
    exact shadow_convex s_convex ⟨out, out_so3⟩
  · change shift '' _ ⊆ _; rw [inner_shadow'_eq]; exact shadow_sub
