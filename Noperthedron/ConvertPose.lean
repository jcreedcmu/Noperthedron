import Noperthedron.MatrixPose
import Noperthedron.ViewPose
import Noperthedron.Pose

def Pose.matrixPoseOfPose (p : Pose) : MatrixPose where
  innerRot := sorry -- TODO(easy)
  outerRot := sorry -- TODO(easy)
  innerOffset := 0

theorem converted_pose_inner_shadow_eq (v : Pose) (S : Set ℝ³) :
    innerShadow v S = innerShadow (v.matrixPoseOfPose) S := by
  sorry -- TODO(easy)

theorem converted_pose_outer_shadow_eq (v : Pose) (S : Set ℝ³) :
    outerShadow v S = outerShadow (v.matrixPoseOfPose) S := by
  sorry -- TODO(easy)

theorem converted_pose_rupert_iff (v : Pose) (S : Set ℝ³) :
    RupertPose v S ↔ RupertPose (v.matrixPoseOfPose) S := by
  constructor; all_goals
  · unfold RupertPose
    rw [converted_pose_inner_shadow_eq, converted_pose_outer_shadow_eq]
    exact id

theorem view_pose_of_pose (p : MatrixPose) : ∃ pp : Pose, pp.matrixPoseOfPose = p.zeroOffset := by
  sorry -- TODO(easy)
