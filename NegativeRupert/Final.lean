import Rupert.Equivalences.RupertEquivRupertSet
import NegativeRupert.Basic
import NegativeRupert.Nopert
import NegativeRupert.ViewPose
import NegativeRupert.ConvertPose
import NegativeRupert.CommonCenter

open scoped Matrix

/--
There is no view pose that makes the Noperthedron have the Rupert property

TODO(hard): prove
-/
theorem no_nopert_view_pose : ¬ ∃ v : ViewPose, Shadows.IsRupert v nopert.hull := by
  sorry

/--
There is no purely rotational pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_rot_pose : ¬ ∃ p : Pose, Shadows.IsRupert p.zeroOffset nopert.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  let ⟨v, e⟩ := view_pose_of_pose p
  refine no_nopert_view_pose ⟨v, ?_⟩
  apply (converted_pose_rupert_iff v nopert.hull).mpr
  rw [e]
  exact r

/--
There is no pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_pose : ¬ ∃ p : Pose, Shadows.IsRupert p nopert.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  have hconvex : Convex ℝ nopert.hull := by
    unfold Shape.hull
    exact convex_convexHull ℝ (Set.range nopert.vertices)
  have r' := rupert_implies_rot_rupert nopert_point_symmetric hconvex p r
  exact no_nopert_rot_pose ⟨p, r'⟩

/--
If a set is Rupert according to the standard definition, then we can package
up the pose parameters. This should be an iff, but I haven't bothered proving
the converse.
-/
lemma rupert_set_implies_pose_rupert {S : Set ℝ³} (r : IsRupertSet S) :
    ∃ p : Pose, Shadows.IsRupert p S := by
  obtain ⟨inner, inner_so3, offset, outer, outer_so3, sub⟩ := r
  let p : Pose := Pose.mk ⟨inner, inner_so3⟩ ⟨outer, outer_so3⟩ offset
  use p
  change closure (Shadows.inner p S) ⊆ interior (Shadows.outer p S)
  rw [p.inner_shadow_lemma]
  exact sub

/--
The Noperthedron (as a subset of ℝ³) is not Rupert
-/
theorem nopert_not_rupert_set : ¬ IsRupertSet nopert.hull := fun r =>
  no_nopert_pose (rupert_set_implies_pose_rupert r)

/--
The Noperthedron is not Rupert
-/
theorem nopert_not_rupert : ¬ IsRupert nopertVerts := fun r =>
  nopert_not_rupert_set ((rupert_iff_rupert_set (nopert.vertices)).mp r)
