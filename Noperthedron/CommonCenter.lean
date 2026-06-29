import Noperthedron.Rupert.Basic
import Noperthedron.Rupert.Set
import Noperthedron.Util
import Noperthedron.MatrixPose
import Noperthedron.PoseClasses
import Noperthedron.PointSym

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

/--
Suppose A and B are both pointsymmetric subsets of ℝ². Suppose B is convex.
If some translate of A is contained in B, then A is contained in B.
-/
theorem common_center {A B : Set ℝ²} (psa : PointSym A) (psb : PointSym B)
    (b_convex : Convex ℝ B)
    (v : ℝ²) (hin : (· + v) '' A ⊆ B) : A ⊆ B := by
  intro a ha
  have h1 : a + v ∈ B := hin ⟨a, ha, rfl⟩
  have h2 : a - v ∈ B := by
    have han : -a ∈ A := psa a ha
    have hnav : -a + v ∈ B := hin ⟨-a, han, rfl⟩
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using psb (-a + v) hnav
  have segment_sub_b := convex_iff_segment_subset.mp b_convex h1 h2
  exact segment_sub_b (mem_segment_add_sub a v)

theorem shadow_outer_pres_convex {S : Set ℝ³} (s_conv : Convex ℝ S) (p : MatrixPose) :
  Convex ℝ (outerShadow p S) := by
  change Convex ℝ ((proj_xyL ∘ PoseLike.outer p) '' S)
  rw [Set.image_comp]
  exact Convex.linear_image (rotation_preserves_convex s_conv p.outerRot)
    (proj_xyL : ℝ³ →L[ℝ] ℝ²).toLinearMap

theorem shadow_outer_pres_psym {S : Set ℝ³} (s_psym : PointSym S) (p : MatrixPose) :
  PointSym (outerShadow p S) := by
  change PointSym ((proj_xyL ∘ PoseLike.outer p) '' S)
  rw [Set.image_comp]
  exact continuousLinearMap_preserves_point_sym proj_xyL
    (rotation_preserves_point_sym s_psym p.outerRot)

theorem shadow_inner_pres_psym {S : Set ℝ³} (s_psym : PointSym S) (p : MatrixPose) :
  PointSym (innerShadow p.zeroOffset S) := by
  change PointSym ((proj_xyL ∘ PoseLike.inner p.zeroOffset) '' S)
  rw [Set.image_comp]
  simp only [MatrixPose.zero_offset_elim]
  exact continuousLinearMap_preserves_point_sym proj_xyL
    (rotation_preserves_point_sym s_psym p.innerRot)

/--
We can pull out the shift baked into innerShadow all the way outside
-/
lemma shadows_eq {S : Set ℝ³} (p : MatrixPose) :
    p.shift '' closure (innerShadow p.zeroOffset S) =
      closure (innerShadow p S) := by
  rw [Homeomorph.image_closure p.shift]
  refine congrArg closure ?_
  change p.shift '' ((proj_xyL ∘ PoseLike.inner p.zeroOffset) '' S) = _
  simp only [MatrixPose.zero_offset_elim]
  rw [← Set.image_comp]
  change ((p.shift ∘ proj_xyL) ∘ p.innerRotPart) '' S =
     ((proj_xyL ∘ p.innerOffsetPart) ∘ p.innerRotPart) '' S
  have : p.shift ∘ proj_xyL = proj_xyL ∘ p.innerOffsetPart := funext fun v ↦ by
    simpa [MatrixPose.shift, MatrixPose.innerOffsetPart] using
      proj_xyL_offset_commute p.innerOffset v
  rw [this]

/--
If a set is point symmetric and convex, then it being rupert implies
being purely rotationally rupert.
-/
theorem rupert_implies_rot_rupert {S : Set ℝ³} (s_sym : PointSym S) (s_convex : Convex ℝ S)
    (p : MatrixPose) (r : RupertPose p S) : RupertPose (p.zeroOffset) S := by
  refine common_center ?_ ?_ ?_ p.innerOffset ?_
  · exact closure_preserves_point_sym (shadow_inner_pres_psym s_sym p)
  · exact interior_preserves_point_sym (shadow_outer_pres_psym s_sym p)
  · exact Convex.interior (shadow_outer_pres_convex s_convex p)
  · change p.shift '' _ ⊆ _
    rw [shadows_eq]
    exact r
