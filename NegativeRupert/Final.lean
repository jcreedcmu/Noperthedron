import NegativeRupert.Rupert.Equivalences.RupertEquivRupertSet
import NegativeRupert.Basic
import NegativeRupert.Nopert
import NegativeRupert.ViewPose
import NegativeRupert.TightViewPose
import NegativeRupert.Tightening
import NegativeRupert.ConvertPose
import NegativeRupert.CommonCenter

open scoped Matrix

/--
There is no tight view pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_tight_view_pose : ¬ ∃ v : ViewPose,
    tightInterval.contains v ∧  Shadows.IsRupert v nopert.hull := by
  sorry -- TODO(hard)

/--
There is no view pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_view_pose : ¬ ∃ v : ViewPose, Shadows.IsRupert v nopert.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  exact no_nopert_tight_view_pose (rupert_tightening p r)

/--
There is no purely rotational pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_rot_pose : ¬ ∃ p : MatrixPose, Shadows.IsRupert p.zeroOffset nopert.hull := by
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
theorem no_nopert_pose : ¬ ∃ p : MatrixPose, Shadows.IsRupert p nopert.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  have hconvex : Convex ℝ nopert.hull := by
    unfold Shape.hull
    exact convex_convexHull ℝ (Set.range nopert.vertices)
  have r' := rupert_implies_rot_rupert nopert_point_symmetric hconvex p r
  exact no_nopert_rot_pose ⟨p, r'⟩

/--
If a set is Rupert according to the standard definition, then we can
package up the pose parameters. The converse also should be true, but
there hasn't been any need for it yet.
-/
lemma rupert_set_implies_pose_rupert {S : Set ℝ³} (r : IsRupertSet S) :
    ∃ p : MatrixPose, Shadows.IsRupert p S := by
  obtain ⟨inner, inner_so3, offset, outer, outer_so3, sub⟩ := r
  let p : MatrixPose := MatrixPose.mk ⟨inner, inner_so3⟩ ⟨outer, outer_so3⟩ offset
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
The Noperthedron is not Rupert.

FIXME: Ideally we'd like to reconcile this with
[https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/Rupert.lean](the
formal-conjectures formulation) which will require some minor
impedance matching, and an extra proof obligation that the interior of
the Noperthedron is nonempty.
-/

theorem nopert_not_rupert : ¬ IsRupert nopertVerts := fun r =>
  nopert_not_rupert_set ((rupert_iff_rupert_set (nopert.vertices)).mp r)
