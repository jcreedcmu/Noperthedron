import NegativeRupert.Basic
import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand
import NegativeRupert.Nopert
import NegativeRupert.MatrixViewRel
import NegativeRupert.CommonCenter

theorem all_nopert_view_cands_safe : ∀ vp : ViewPose, (nopertViewCand vp).Safe := by
 sorry

theorem all_nopert_matrix_cands_safe : ∀ mp : MatrixPose, (nopertCand mp).Safe := by
  intros mp
  let ⟨ vp, hvp ⟩ := exists_nopert_view_equiv mp
  have hs : (nopertViewCand vp).Safe := all_nopert_view_cands_safe vp
  exact equiv_preserves_safety (nopertCand mp) (nopertViewCand vp) hvp hs

theorem nopert_cube_not_rupert : ¬ IsRupert nopertCube.vertices := by
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
  obtain ⟨y, hy, hy'⟩ := all_nopert_matrix_cands_safe mp
  use y
  exact ⟨hy, fun hy2 ↦ hy' (interior_subset hy2)⟩
