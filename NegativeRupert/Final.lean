import NegativeRupert.Basic
import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand

def snubCube : Shape := sorry

def snubCand (mp : MatrixPose) : MatrixCand :=
  { pose := mp
    shape := snubCube }

theorem all_snub_cands_safe : ∀ mp : MatrixPose, (snubCand mp).Safe := by
 sorry

theorem snub_cube_not_rupert : ¬ IsRupert snubCube.vertices := by
  unfold IsRupert
  push_neg
  intros innerRot inner_rot_so3 innerOffset outerRot outer_rot_so3
  lift_lets
  intros hull inner_shadow outer_shadow
  refine Set.not_subset.mpr ?_
  let mp : MatrixPose := {
    innerRot := ⟨innerRot, inner_rot_so3⟩,
    outerRot := ⟨outerRot, outer_rot_so3⟩,
    innerOffset,
  }
  obtain ⟨y, hy, hy'⟩ := all_snub_cands_safe mp
  use y
  exact ⟨hy, fun hy2 ↦ hy' (interior_subset hy2)⟩
