import Rupert.Equivalences.RupertEquivRupertSet
import NegativeRupert.Basic
import NegativeRupert.Nopert
import NegativeRupert.CommonCenter

open scoped Matrix

/--
If a set is Rupert according to the standard definition, then we can package
up the pose parameters. This should be an iff, but I haven't bothered proving
the converse.
-/
theorem rupert_set_implies_pose_rupert {S : Set ℝ³} (r : IsRupertSet S) :
    ∃ p : Pose, Shadows.IsRupert p S := by
  obtain ⟨inner, inner_so3, offset, outer, outer_so3, sub⟩ := r
  let p : Pose := Pose.mk ⟨inner, inner_so3⟩ ⟨outer, outer_so3⟩ offset
  use p
  change closure (Shadows.inner p S) ⊆ interior (Shadows.outer p S)
  rw [p.inner_shadow_lemma]
  exact sub

/--
There is no purely rotational pose that makes the Noperthedron (as a
subset of ℝ³) have the Rupert property

TODO(hard): prove
-/
theorem no_nopert_rot_pose : ¬ ∃ p : Pose, Shadows.IsRupert (p.zero_offset) nopert.hull := by
  sorry

/--
There is no pose that makes the Noperthedron (as a subset of ℝ³) have the Rupert property
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
The Noperthedron (as a subset of ℝ³) is not Rupert
-/
theorem nopert_not_rupert_set : ¬ IsRupertSet nopert.hull := fun r =>
  no_nopert_pose (rupert_set_implies_pose_rupert r)

/--
The Noperthedron is not Rupert
-/
theorem nopert_not_rupert : ¬ IsRupert nopertVerts := fun r =>
  nopert_not_rupert_set ((rupert_iff_rupert_set (nopert.vertices)).mp r)
