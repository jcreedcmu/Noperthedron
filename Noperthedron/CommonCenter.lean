import Noperthedron.Rupert.Basic
import Noperthedron.Rupert.Set
import Noperthedron.Util
import Noperthedron.MatrixPose
import Noperthedron.PoseClasses

/-
This file more or less captures Proposition 2 from
"An algorithmic approach to Rupert's problem"
[Steininger, Yurkevich 2021]
https://arxiv.org/pdf/2112.13754

The crux is that if a polyhedron (or indeed any convex set) S is
pointsymmetric (i.e. invariant under x ↦ -x) then the question of
whether S is Rupert can, without loss, be analyzed by only considering
rotations, and ignoring translations.
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
  exact segment_sub_b (mem_segment_add_sub a v)

theorem shadow_outer_pres_convex {S : Set ℝ³} (s_conv : Convex ℝ S) (p : MatrixPose) :
  Convex ℝ (Shadows.outer p S) := by
  change Convex ℝ (proj_xy ∘ Affines.outer p '' S)
  rw [Set.image_comp]
  exact proj_pres_convex (rotation_pres_convex s_conv p.outerRot)

theorem shadow_outer_pres_psym {S : Set ℝ³} (s_psym : PointSym S) (p : MatrixPose) :
  PointSym (Shadows.outer p S) := by
  change PointSym (proj_xy ∘ Affines.outer p '' S)
  rw [Set.image_comp]
  exact proj_pres_point_sym (rotation_pres_point_sym (s_psym) p.outerRot)

theorem shadow_inner_pres_psym {S : Set ℝ³} (s_psym : PointSym S) (p : MatrixPose) :
  PointSym (Shadows.inner p.zeroOffset S) := by
  change PointSym (proj_xy ∘ Affines.inner p.zeroOffset '' S)
  rw [Set.image_comp]
  refine proj_pres_point_sym ?_
  simp only [MatrixPose.zero_offset_elim]
  exact rotation_pres_point_sym s_psym p.innerRot

/--
We can pull out the shift baked into Shadows.inner all the way outside
-/
lemma shadows_eq {S : Set ℝ³} (p : MatrixPose) :
    p.shift '' closure (Shadows.inner p.zeroOffset S) =
      closure (Shadows.inner p S) := by
  rw [Homeomorph.image_closure p.shift]
  refine congrArg closure ?_
  change p.shift '' ((proj_xy ∘ Affines.inner p.zeroOffset) '' S) = _
  simp only [MatrixPose.zero_offset_elim]
  rw [← Set.image_comp]
  change ((p.shift ∘ proj_xy) ∘ p.innerRotPart) '' S =
     ((proj_xy ∘ p.innerOffsetPart) ∘ p.innerRotPart) '' S
  rw [show p.shift ∘ proj_xy = proj_xy ∘ p.innerOffsetPart from funext fun v ↦
    proj_offset_commute _ _]

/--
If a set is point symmetric and convex, then it being rupert implies
being purely rotationally rupert.
-/
theorem rupert_implies_rot_rupert {S : Set ℝ³} (s_sym : PointSym S) (s_convex : Convex ℝ S)
    (p : MatrixPose) (r : Shadows.IsRupert p S) : Shadows.IsRupert (p.zeroOffset) S := by
  refine common_center ?_ ?_ ?_ p.innerOffset ?_
  · exact closure_pres_point_sym (shadow_inner_pres_psym s_sym p)
  · exact interior_pres_point_sym (shadow_outer_pres_psym s_sym p)
  · exact Convex.interior (shadow_outer_pres_convex s_convex p)
  · change p.shift '' _ ⊆ _
    rw [shadows_eq]
    exact r
