import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet
import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Tightening
import Noperthedron.ConvertPose
import Noperthedron.CommonCenter
import Noperthedron.ComputationalStep
import Noperthedron.Vertices.Exact

open scoped Matrix

namespace Noperthedron

/--
There is no tight pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_tight_pose : ¬ ∃ v : Pose,
    tightInterval.contains v ∧ RupertPose v exactShape.hull := by
  rintro ⟨v, h1, h2⟩
  let ⟨tab, htab, hz, tight⟩ := exists_solution_table
  exact Solution.Row.valid_imp_not_rupert tab htab hz ⟨v, tight v h1, h2⟩

/--
There is no pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_pose : ¬ ∃ v : Pose, RupertPose v exactShape.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  exact no_nopert_tight_pose (Tightening.rupert_tightening p r)

/--
There is no purely rotational pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_rot_pose : ¬ ∃ p : MatrixPose, RupertPose p.zeroOffset exactShape.hull := by
  rintro ⟨p, r⟩
  obtain ⟨δ, v, e⟩ := pose_of_matrix_pose p
  exact no_nopert_pose ⟨v, (converted_pose_rupert_iff v exactShape.hull).mpr <|
    e ▸ (MatrixPose.RupertPose_rotateBy_iff p.zeroOffset δ exactShape.hull).mpr r⟩

/--
There is no pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_matrix_pose : ¬ ∃ p : MatrixPose, RupertPose p exactShape.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  have hconvex : Convex ℝ exactShape.hull := by
    unfold Shape.hull
    exact convex_convexHull ℝ (↑exactShape.vertices : Set ℝ³)
  have r' := rupert_implies_rot_rupert exactShape_point_symmetric hconvex p r
  exact no_nopert_rot_pose ⟨p, r'⟩

/--
If a set is Rupert according to the standard definition, then we can
package up the pose parameters. The converse also should be true, but
there hasn't been any need for it yet.
-/
lemma rupert_set_implies_pose_rupert {S : Set ℝ³} (r : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, inner_so3, offset, outer, outer_so3, sub⟩ := r
  let p : MatrixPose := MatrixPose.mk ⟨inner, inner_so3⟩ ⟨outer, outer_so3⟩ offset
  use p
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  rw [p.inner_shadow_lemma, outerShadow]
  repeat rw [← proj_xy_eq_proj_xyL]
  exact sub

/--
The Noperthedron (as a subset of ℝ³) is not Rupert
-/
theorem nopert_not_rupert_set : ¬ IsRupertSet exactShape.hull := fun r =>
  no_nopert_matrix_pose (rupert_set_implies_pose_rupert r)

/--
The Noperthedron is not Rupert.
-/
theorem nopert_not_rupert : ¬ IsRupert exactVerts := by
  intro r
  refine nopert_not_rupert_set ?_
  exact rupert_iff_rupert_set exactVerts |>.mp r
