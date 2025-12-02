import Noperthedron.Basic
import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Util

open scoped Matrix

structure MatrixPose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

namespace MatrixPose

def IsRot (p : MatrixPose) : Prop :=
  p.innerOffset = 0

def zeroOffset (p : MatrixPose) : MatrixPose :=
  { p with innerOffset := 0 }

noncomputable def innerOffsetPart (p : MatrixPose) : ℝ³ → ℝ³ :=
  translationAffineEquiv (inject_xy p.innerOffset)
noncomputable def innerRotPart (p : MatrixPose) : ℝ³ → ℝ³ := p.innerRot.val.toEuclideanLin

end MatrixPose

noncomputable
instance : PoseLike MatrixPose where
  inner p := (translationAffineEquiv (inject_xy p.innerOffset)).toAffineMap.comp
      (p.innerRot.val.toEuclideanLin.toAffineMap)
  outer p := p.outerRot.val.toEuclideanLin.toAffineMap

namespace MatrixPose

/--
If we zero out the offset, then the offset part of the inner
action is the identity.
-/
theorem zero_offset_id (p : MatrixPose) (v : ℝ³) : p.zeroOffset.innerOffsetPart v = v := by
  ext i; fin_cases i
  all_goals
    change (translationAffineEquiv 0) v _ = v _
    unfold translationAffineEquiv;
    simp

@[simp]
theorem zero_offset_elim (p : MatrixPose) :
    ↑(PoseLike.inner p.zeroOffset) = (fun (v : ℝ³) => p.innerRot.val.toEuclideanLin v) := by
  ext1 v
  change p.zeroOffset.innerOffsetPart (p.innerRot.val.toEuclideanLin v) = _
  rw [zero_offset_id]

noncomputable def shift (p : MatrixPose) : ℝ² ≃ₜ ℝ² := translationHomeo p.innerOffset

/--
We can massage innerShadow p S into the form of the standard Rupert definition
-/
theorem inner_shadow_lemma (p : MatrixPose) (S : Set ℝ³) :
    innerShadow p S = {x | ∃ v ∈ S, p.innerOffset + proj_xyL (p.innerRot.val.toEuclideanLin v) = x} := by
  change ((proj_xyL ∘ (· + inject_xy p.innerOffset)) ∘ p.innerRotPart) '' S =
         (((p.innerOffset + ·) ∘ proj_xyL) ∘ p.innerRotPart) '' S
  suffices h : proj_xyL ∘ (· + inject_xy p.innerOffset) = (p.innerOffset + ·) ∘ proj_xyL by
    rw[h]
  ext1 v
  simp only [Function.comp_apply]
  nth_rw 2 [add_comm]
  rw [← proj_xy_eq_proj_xyL, proj_offset_commute p.innerOffset v]

end MatrixPose
