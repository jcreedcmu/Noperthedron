import NegativeRupert.Pose
import NegativeRupert.ViewPose

def poseOfViewPose (v : ViewPose) : Pose where
  innerRot := sorry -- TODO(easy)
  outerRot := sorry -- TODO(easy)
  innerOffset := 0

theorem converted_pose_inner_shadow_eq (v : ViewPose) (S : Set ℝ³) :
    Shadows.inner v S = Shadows.inner (poseOfViewPose v) S := by
  sorry -- TODO(easy)

theorem converted_pose_outer_shadow_eq (v : ViewPose) (S : Set ℝ³) :
    Shadows.outer v S = Shadows.outer (poseOfViewPose v) S := by
  sorry -- TODO(easy)

theorem converted_pose_rupert_iff (v : ViewPose) (S : Set ℝ³) :
    Shadows.IsRupert v S ↔ Shadows.IsRupert (poseOfViewPose v) S := by
  constructor; all_goals
  · unfold Shadows.IsRupert
    rw [converted_pose_inner_shadow_eq, converted_pose_outer_shadow_eq]
    exact id

theorem view_pose_of_pose (p : Pose) : ∃ v : ViewPose, poseOfViewPose v = p.zeroOffset := by
  sorry -- TODO(easy)
