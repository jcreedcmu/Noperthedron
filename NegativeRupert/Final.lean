import NegativeRupert.Basic
import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand
import NegativeRupert.Snub
import NegativeRupert.MatrixViewRel

theorem all_snub_view_cands_safe : ∀ vp : ViewPose, (snubViewCand vp).Safe := by
 sorry

theorem all_snub_matrix_cands_safe : ∀ mp : MatrixPose, (snubCand mp).Safe := by
  intros mp
  let ⟨ vp, hvp ⟩ := exists_snub_view_equiv mp
  have hs : (snubViewCand vp).Safe := all_snub_view_cands_safe vp
  exact equiv_preserves_safety (snubCand mp) (snubViewCand vp) hvp hs

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
  obtain ⟨y, hy, hy'⟩ := all_snub_matrix_cands_safe mp
  use y
  exact ⟨hy, fun hy2 ↦ hy' (interior_subset hy2)⟩
