# PR: Rz-Invariance of RupertPose

## Summary

Proves that `RupertPose` is invariant under Rz rotation, eliminating the sorry in `no_nopert_rot_pose`.

## Key Changes

### OrthEquivRotz.lean
- Added rotation helper lemmas (`Rz_mat_transpose`, `Ry_mat_transpose`, etc.)
- Proved `Rz_mat_mul_Rz_mat` (rotation composition) - golfed to 2 lines
- Proved `SO3_ZYZ_decomposition` (any SO3 = Rz(α) * Ry(β) * Rz(γ)) - no maxHeartbeats override needed
- Added `@[simp] Rz_mat_zero`, `rotRM_mat_zero_alpha`, `exists_Rz_to_rotRM_form`

### Basic.lean
- Added `@[simp]` to `proj_xyL_comp_RzL`

### MatrixPose.lean
- Added `rotateBy` definition (rotate both rotations and offset by Rz(δ))
- Proved `innerShadow_rotateBy`, `outerShadow_rotateBy` (shadows rotate with rotR)
- Proved `RupertPose_rotateBy_iff` (RupertPose is Rz-invariant)
- Golfed `Rz_mul_toEuclideanLin` (terminal simp)

### ConvertPose.lean
- Filled `Pose.matrixPoseOfPose` using `rotRM_mat`
- Filled `converted_pose_inner_shadow_eq`, `converted_pose_outer_shadow_eq` - golfed with `<;>` combinator
- Added `SO3_to_rotRM_params` (any SO3 is rotRM_mat form) - golfed
- Added `@[simp] inject_xy_zero`, `@[simp] zeroOffset_rotateBy_zeroOffset`
- Updated `pose_of_matrix_pose` to return rotation angle δ and Pose - golfed with `simpa`

### Final.lean
- Updated `no_nopert_rot_pose` to use Rz-invariance via `RupertPose_rotateBy_iff`

## Test Plan
- `lake build` passes
- No new sorries introduced in modified files
