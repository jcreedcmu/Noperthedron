import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand
import NegativeRupert.Snub

/-
This file manages the relationship between matrix-format candidates and view-format candidates.
-/

def matrix_of_view (vp : ViewPose) : MatrixPose :=
  let { innerView, outerView, innerSpin, innerOffset } := vp
  { innerRot := sorry,
    outerRot := sorry,
    innerOffset }

/--
Two candidates in different formats are equivalent if they have the same shape and the same shadows.
-/
def equiv_cand (mc : MatrixCand) (vc : ViewCand) : Prop :=
  mc.shape = vc.shape ∧ mc.outerShadow = vc.outerShadow ∧ mc.innerShadow = vc.innerShadow

/--
Equivalence across format preserves the property of being "safe".
-/
theorem equiv_preserves_safety (mc : MatrixCand) (vc : ViewCand)
    (ec : equiv_cand mc vc) (vc_safe : vc.Safe) : mc.Safe := by
  let ⟨shape_equiv, outer_eq, inner_eq⟩ := ec
  change ∃ y ∈ mc.innerShadow, y ∉ mc.outerShadow
  rw [inner_eq, outer_eq]
  exact vc_safe

/--
For the snub cube specifically, for any matrix pose there is a
view pose that induces an equivalence. Assuming view poses actually
exclude the straight-down-the-barrel-of-the-z-axis pose, this relies
on octagonal symmetry of the snub cube.
-/
theorem exists_snub_view_equiv (mp : MatrixPose) : ∃ vp : ViewPose,
    equiv_cand (snubCand mp) (snubViewCand vp) := sorry
