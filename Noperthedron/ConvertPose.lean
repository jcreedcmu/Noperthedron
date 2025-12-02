import Noperthedron.MatrixPose
import Noperthedron.ViewPose

def poseOfViewPose (v : ViewPose) : MatrixPose where
  innerRot := sorry -- TODO(easy)
  outerRot := sorry -- TODO(easy)
  innerOffset := 0

theorem converted_pose_inner_shadow_eq (v : ViewPose) (S : Set ℝ³) :
    innerShadow v S = innerShadow (poseOfViewPose v) S := by
  sorry -- TODO(easy)

theorem converted_pose_outer_shadow_eq (v : ViewPose) (S : Set ℝ³) :
    outerShadow v S = outerShadow (poseOfViewPose v) S := by
  sorry -- TODO(easy)

theorem converted_pose_rupert_iff (v : ViewPose) (S : Set ℝ³) :
    RupertPose v S ↔ RupertPose (poseOfViewPose v) S := by
  constructor; all_goals
  · unfold RupertPose
    rw [converted_pose_inner_shadow_eq, converted_pose_outer_shadow_eq]
    exact id

theorem view_pose_of_pose (p : MatrixPose) : ∃ v : ViewPose, poseOfViewPose v = p.zeroOffset := by
  sorry -- TODO(easy)
