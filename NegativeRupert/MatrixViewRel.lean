import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand

/-
This file manages the relationship between matrix-format candidates and view-format candidates.
-/

def matrix_of_view (vp : ViewPose) : MatrixPose :=
  let { innerView, outerView, innerSpin, innerOffset } := vp
  { innerRot := sorry,
    outerRot := sorry,
    innerOffset }

def equiv_cand (mc : MatrixCand) (vc : ViewCand) : Prop :=
  mc.outerShadow = vc.outerShadow ∧ mc.innerShadow = vc.innerShadow
