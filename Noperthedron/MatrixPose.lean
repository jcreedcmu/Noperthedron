module

public import Noperthedron.Basic
public import Noperthedron.Rupert.Basic
public import Noperthedron.PoseClasses

@[expose] public section

open scoped Matrix

structure MatrixPose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

namespace MatrixPose

def zeroOffset (p : MatrixPose) : MatrixPose :=
  { p with innerOffset := 0 }

/-- The xy-projection of the rotation `M`, as a continuous linear map `ℝ³ →L[ℝ] ℝ²`. -/
noncomputable def projRot (M : SO3) : ℝ³ →L[ℝ] ℝ² :=
  proj_xyL ∘L M.val.toEuclideanLin.toContinuousLinearMap

end MatrixPose

noncomputable
instance : PoseLike MatrixPose where
  inner p := (AffineEquiv.vaddConst ℝ p.innerOffset).toAffineMap.comp
      (MatrixPose.projRot p.innerRot).toAffineMap
  outer p := (MatrixPose.projRot p.outerRot).toAffineMap

namespace MatrixPose

lemma inner_apply (p : MatrixPose) (v : ℝ³) :
    PoseLike.inner p v = projRot p.innerRot v + p.innerOffset := rfl

lemma outer_apply (p : MatrixPose) (v : ℝ³) :
    PoseLike.outer p v = projRot p.outerRot v := rfl

@[simp]
theorem zero_offset_elim (p : MatrixPose) :
    ⇑(PoseLike.inner p.zeroOffset) = ⇑(projRot p.innerRot) := by
  funext v
  rw [inner_apply]
  exact add_zero _

noncomputable def shift (p : MatrixPose) : ℝ² ≃ₜ ℝ² := Homeomorph.addRight p.innerOffset

/-- The inner shadow is the shifted inner shadow of the zero-offset pose. -/
theorem innerShadow_eq_shift (p : MatrixPose) (S : Set ℝ³) :
    innerShadow p S = p.shift '' innerShadow p.zeroOffset S := by
  simp only [innerShadow, zero_offset_elim, ← Set.image_comp]
  rfl

/-- rotR composition is addition of angles. -/
lemma rotR_comp (α β : ℝ) : (rotR α).comp (rotR β) = rotR (α + β) :=
  (AddChar.map_add_eq_mul rotR α β).symm

/-- rotR as a continuous linear equiv. -/
noncomputable def rotR_equiv (δ : ℝ) : ℝ² ≃L[ℝ] ℝ² :=
  ContinuousLinearEquiv.equivOfInverse (rotR δ) (rotR (-δ))
    (fun v => by rw [← ContinuousLinearMap.comp_apply, rotR_comp, neg_add_cancel,
      AddChar.map_zero_eq_one, one_apply_eq_self])
    (fun v => by rw [← ContinuousLinearMap.comp_apply, rotR_comp, add_neg_cancel,
      AddChar.map_zero_eq_one, one_apply_eq_self])

end MatrixPose

end
