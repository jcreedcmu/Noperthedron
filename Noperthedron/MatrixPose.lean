module

public import Noperthedron.Basic
public import Noperthedron.Rupert.Basic
public import Noperthedron.PoseClasses
public import Noperthedron.Bounding.OrthEquivRotz

@[expose] public section


open scoped Matrix

structure MatrixPose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

namespace MatrixPose

def zeroOffset (p : MatrixPose) : MatrixPose :=
  { p with innerOffset := 0 }

/-- Rotate a MatrixPose by applying Rz(δ) to both rotations and the offset. -/
noncomputable def rotateBy (p : MatrixPose) (δ : ℝ) : MatrixPose where
  innerRot := ⟨Rz_mat δ * p.innerRot.val,
    Submonoid.mul_mem _ (Bounding.rot3_mat_mem_SO3 2 δ) p.innerRot.property⟩
  outerRot := ⟨Rz_mat δ * p.outerRot.val,
    Submonoid.mul_mem _ (Bounding.rot3_mat_mem_SO3 2 δ) p.outerRot.property⟩
  innerOffset := rotR δ p.innerOffset

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

/-- Matrix multiplication yields RzL composition. -/
lemma Rz_mul_toEuclideanLin (δ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    (Rz_mat δ * M).toEuclideanLin v = RzL δ (M.toEuclideanLin v) := by
  simp [Matrix.toLpLin_apply, RzL, Matrix.mulVec_mulVec]

lemma projRot_Rz_mul (δ : ℝ) (M : SO3) (h) :
    projRot ⟨Rz_mat δ * M.val, h⟩ = rotR δ ∘L projRot M := by
  ext1 v
  simp only [projRot, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    Rz_mul_toEuclideanLin]
  exact ContinuousLinearMap.ext_iff.mp (proj_xyL_comp_RzL δ) _

lemma projRot_rotateBy_inner (p : MatrixPose) (δ : ℝ) :
    projRot (p.rotateBy δ).innerRot = rotR δ ∘L projRot p.innerRot :=
  projRot_Rz_mul δ p.innerRot _

lemma projRot_rotateBy_outer (p : MatrixPose) (δ : ℝ) :
    projRot (p.rotateBy δ).outerRot = rotR δ ∘L projRot p.outerRot :=
  projRot_Rz_mul δ p.outerRot _

lemma inner_rotateBy (p : MatrixPose) (δ : ℝ) :
    ⇑(PoseLike.inner (p.rotateBy δ)) = rotR δ ∘ PoseLike.inner p := by
  funext v
  change projRot (p.rotateBy δ).innerRot v + rotR δ p.innerOffset =
    rotR δ (projRot p.innerRot v + p.innerOffset)
  rw [map_add, projRot_rotateBy_inner]
  rfl

lemma outer_rotateBy (p : MatrixPose) (δ : ℝ) :
    ⇑(PoseLike.outer (p.rotateBy δ)) = rotR δ ∘ PoseLike.outer p := by
  funext v
  change projRot (p.rotateBy δ).outerRot v = rotR δ (projRot p.outerRot v)
  rw [projRot_rotateBy_outer]
  rfl

/-- Outer shadow of rotated pose equals rotated outer shadow. -/
theorem outerShadow_rotateBy (p : MatrixPose) (δ : ℝ) (S : Set ℝ³) :
    outerShadow (p.rotateBy δ) S = rotR δ '' outerShadow p S := by
  simp only [outerShadow, outer_rotateBy, Set.image_comp]

/-- Inner shadow of rotated pose equals rotated inner shadow. -/
theorem innerShadow_rotateBy (p : MatrixPose) (δ : ℝ) (S : Set ℝ³) :
    innerShadow (p.rotateBy δ) S = rotR δ '' innerShadow p S := by
  simp only [innerShadow, inner_rotateBy, Set.image_comp]

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

/-- rotR as a homeomorphism. -/
noncomputable def rotR_homeomorph (δ : ℝ) : ℝ² ≃ₜ ℝ² := (rotR_equiv δ).toHomeomorph

/-- RupertPose is invariant under rotation by Rz(δ). -/
theorem RupertPose_rotateBy_iff (p : MatrixPose) (δ : ℝ) (S : Set ℝ³) :
    RupertPose (p.rotateBy δ) S ↔ RupertPose p S := by
  simp only [RupertPose, innerShadow_rotateBy, outerShadow_rotateBy,
    show (fun a => rotR δ a) = rotR_homeomorph δ from rfl]
  rw [← Homeomorph.image_closure (rotR_homeomorph δ), ← Homeomorph.image_interior (rotR_homeomorph δ)]
  exact Set.image_subset_image_iff (rotR_homeomorph δ).injective

end MatrixPose

end
