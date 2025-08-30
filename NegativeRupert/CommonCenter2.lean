import Rupert.Basic
import Rupert.Set
import NegativeRupert.RotRupert
import NegativeRupert.Util

/-
This file more or less captures Proposition 2 from
"An algorithmic approach to Rupert's problem"
[Steininger, Yurkevich 2021]
https://arxiv.org/pdf/2112.13754

The crux is that if a polyhedron (or indeed any convex set) S is
pointsymmetric (i.e. invariant under x ↦ -x) then the question of
whether S is Rupert can, without loss, be analyzed by only considering
rotations, and ignoring translations.

This is meant to replace CommonCenter.lean once I finish refactoring...
-/

open scoped Matrix

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
If a set is point symmetric and convex, then it being rupert implies
being purely rotationally rupert.
-/
theorem rupert_implies_rot_rupert {S : Set ℝ³} (s_sym : PointSym S) (s_convex : Convex ℝ S)
    (p : Pose) (r : Shadows.IsRupert p S) : Shadows.IsRupert (p.zero_offset) S := by

  let p' := p.zero_offset
  let inner_shadow' := Shadows.inner p' S

  let shadow_sub := r
  unfold Shadows.IsRupert at shadow_sub ⊢

  let off := p.innerOffset
  let shift := translationHomeo p.innerOffset
  let pose := p
  let pose' := p'

  have inner_shadow'_eq : shift '' closure (Shadows.inner p' S) = closure (Shadows.inner p S) := by
    rw [Homeomorph.image_closure shift]
    refine congrArg closure ?_
    change shift '' ((proj_xy ∘ Affines.inner p.zero_offset) '' S) = _

    change _ '' ((fun v => 0 + proj_xy (pose.innerRot *ᵥ v)) '' S) = _
  --   rw [← Set.image_comp]
  --   change (fun p ↦ (0 + proj_xy _) + off) '' _ = _
  --   conv => lhs; lhs; intro p; rw [zero_add, add_comm]
  --   rfl
    sorry
  change closure (Shadows.inner p S) ⊆ interior (Shadows.outer p S) at shadow_sub
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
