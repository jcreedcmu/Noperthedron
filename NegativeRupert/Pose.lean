import Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Util

open scoped Matrix

structure Pose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

def inject_xy (v : ℝ²) : ℝ³ := fun i => match i with
 | 0 => v 0
 | 1 => v 1
 | 2 => 0

namespace Pose

@[deprecated "should use Shadows instead" (since := "2025-08-30")]
def outerShadow (p : Pose) (s : Set ℝ³) : Set ℝ² :=
  { proj_xy (p.outerRot *ᵥ v) | v ∈ s }

@[deprecated "should use Shadows instead" (since := "2025-08-30")]
def innerShadow (p : Pose) (s : Set ℝ³) : Set ℝ² :=
  { p.innerOffset + proj_xy (p.innerRot *ᵥ v) | v ∈ s }

/--
A candidate is "safe" if it does not admit a Rupert solution.
-/
@[deprecated "should use Shadows instead" (since := "2025-08-30")]
def IsRupert (p : Pose) (s : Set ℝ³) : Prop :=
  closure (p.innerShadow s) ⊆ interior (p.outerShadow s)

/--
A pose is "safe" if it decisively does not admit a Rupert solution.
-/
@[deprecated "should use Shadows instead" (since := "2025-08-30")]
def Safe (p : Pose) (s : Set ℝ³) : Prop :=
  ∃ y, y ∈ p.innerShadow s ∧ ¬ y ∈ p.outerShadow s

def IsRot (p : Pose) : Prop :=
  p.innerOffset = 0

def zero_offset (p : Pose) : Pose :=
  { p with innerOffset := 0 }

def inner_offset_part (p : Pose) : ℝ³ → ℝ³ := (translationAffineEquiv (inject_xy p.innerOffset))
def inner_rot_part (p : Pose) : ℝ³ → ℝ³ := fun v => p.innerRot *ᵥ v

end Pose

noncomputable
instance : Affines Pose where
  inner p := (translationAffineEquiv (inject_xy p.innerOffset)).toAffineMap.comp
      ((Matrix.mulVecLin p.innerRot).toAffineMap)
  outer p := (Matrix.mulVecLin p.outerRot).toAffineMap

theorem zero_offset_only_inner (p : Pose) : Shadows.outer (p.zero_offset) = Shadows.outer p := by
  rfl

theorem pose_ext2 (p : Pose) (v : ℝ³) :
    Affines.inner p v = p.inner_offset_part (p.inner_rot_part v) :=
  by rfl

theorem pose_ext (p : Pose) (v : ℝ³) :
    Affines.inner p v = (translationAffineEquiv (inject_xy p.innerOffset)).toAffineMap.comp
      ((Matrix.mulVecLin p.innerRot).toAffineMap) v :=
  by rfl

theorem proj_offset_commute (t : ℝ²) (v : ℝ³) : (proj_xy v) + t = proj_xy (v + inject_xy t) := by
 sorry

theorem zero_offset_id (p : Pose) (v : ℝ³) : p.zero_offset.inner_offset_part v = v := by
 sorry

@[simp]
theorem zero_offset_elim (p : Pose) :
    ↑(Affines.inner p.zero_offset) = (fun (v : ℝ³) => p.innerRot *ᵥ v) := by
  ext1 v
  change p.zero_offset.inner_offset_part (p.innerRot *ᵥ v) = _
  rw [zero_offset_id]
