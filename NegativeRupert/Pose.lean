import Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Util

open scoped Matrix

structure Pose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

namespace Pose

def IsRot (p : Pose) : Prop :=
  p.innerOffset = 0

def zeroOffset (p : Pose) : Pose :=
  { p with innerOffset := 0 }

noncomputable def innerOffsetPart (p : Pose) : ℝ³ → ℝ³ :=
  translationAffineEquiv (inject_xy p.innerOffset)
def innerRotPart (p : Pose) : ℝ³ → ℝ³ := fun v => p.innerRot *ᵥ v

end Pose

noncomputable
instance : Affines Pose where
  inner p := (translationAffineEquiv (inject_xy p.innerOffset)).toAffineMap.comp
      ((Matrix.mulVecLin p.innerRot).toAffineMap)
  outer p := (Matrix.mulVecLin p.outerRot).toAffineMap

namespace Pose

/--
If we zero out the offset, then the offset part of the inner
action is the identity.
-/
theorem zero_offset_id (p : Pose) (v : ℝ³) : p.zeroOffset.innerOffsetPart v = v := by
  let z : ℝ³ := fun i => match i with
        | 0 => 0
        | 1 => 0
        | 2 => 0
  have z_is_zero : z = 0 := by ext i; fin_cases i <;> rfl
  ext i; fin_cases i
  all_goals
    change (translationAffineEquiv z) v _ = v _
    rw [z_is_zero]; unfold translationAffineEquiv;
    simp

@[simp]
theorem zero_offset_elim (p : Pose) :
    ↑(Affines.inner p.zeroOffset) = (fun (v : ℝ³) => p.innerRot *ᵥ v) := by
  ext1 v
  change p.zeroOffset.innerOffsetPart (p.innerRot *ᵥ v) = _
  rw [zero_offset_id]

noncomputable def shift (p : Pose) : ℝ² ≃ₜ ℝ² := translationHomeo p.innerOffset

/--
We can massage Shadows.inner p S into the form of the standard Rupert definition
-/
theorem inner_shadow_lemma (p : Pose) (S : Set ℝ³) :
    Shadows.inner p S = {x | ∃ v ∈ S, p.innerOffset + proj_xy (p.innerRot *ᵥ v) = x} := by
  change ((proj_xy ∘ (· + inject_xy p.innerOffset)) ∘ p.innerRotPart) '' S =
         (((p.innerOffset + ·) ∘ proj_xy) ∘ p.innerRotPart) '' S
  suffices h : proj_xy ∘ (· + inject_xy p.innerOffset) = (p.innerOffset + ·) ∘ proj_xy by
    rw[h]
  ext1 v
  simp only [Function.comp_apply]
  nth_rw 2 [add_comm]
  rw [proj_offset_commute p.innerOffset v]

end Pose
