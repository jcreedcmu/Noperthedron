module

public import Noperthedron.SnubDodecahedron.AtlasIcoPrune
public import Noperthedron.SnubDodecahedron.IcoModel

@[expose] public section

/-!
# Reducing the relative rotation modulo I

For an `IModel` (whose hull every rotation of I preserves), composing the
inner copy with g ∈ I changes neither shadow, so the relative rotation can
be moved into the icosahedral max-trace cell (README.md, "Symmetry reductions",
reduction 1). `IcoView.IModel.exists_ico_full_atlas_translated_pose` combines
it with the view reduction.
-/

namespace Noperthedron.SnubDodecahedron

open scoped Matrix
open CayleyAtlas

noncomputable def icoSO3 (g : IcoIndex) : SO3 := ⟨icoMatrix g, icoMatrix_mem_SO3 g⟩

/-- Compose only the inner rotation with a rotation of I. -/
noncomputable def _root_.MatrixPose.rightIcoSymmetry (p : MatrixPose) (g : IcoIndex) :
    MatrixPose where
  innerRot := p.innerRot * icoSO3 g
  outerRot := p.outerRot
  innerOffset := p.innerOffset

@[simp] theorem MatrixPose.relativeRotation_rightIcoSymmetry (p : MatrixPose) (g : IcoIndex) :
    (p.rightIcoSymmetry g).relativeRotation = p.relativeRotation * icoMatrix g := by
  simp [MatrixPose.relativeRotation, MatrixPose.rightIcoSymmetry, icoSO3, Matrix.mul_assoc]

/-- The icosahedral cell condition carried by an atlas representative. -/
def AtlasPose.InIcoFundamentalDomain (p : AtlasPose ℝ) (chart : ChartIndex) : Prop :=
  Noperthedron.SnubDodecahedron.InIcoFundamentalDomain (chartMatrix chart * cayleyMatrix p.x p.y p.z)

theorem AtlasPose.InIcoFundamentalDomain.toFivefold {p : AtlasPose ℝ} {chart : ChartIndex}
    (h : p.InIcoFundamentalDomain chart) : p.InFivefoldFundamentalDomain chart :=
  Noperthedron.SnubDodecahedron.InIcoFundamentalDomain.toFivefold (R := chartMatrix chart * cayleyMatrix p.x p.y p.z) h

namespace IModel

variable (P : IModel)

theorem innerShadow_rightIcoSymmetry (p : MatrixPose) (g : IcoIndex) :
    innerShadow (p.rightIcoSymmetry g) P.toC5.polyhedron.hull =
      innerShadow p P.toC5.polyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (icoMatrix g).toEuclideanLin v ∈ P.toC5.polyhedron.hull := by
      rw [← P.icoMatrix_image_hull g]
      exact ⟨v, hv, rfl⟩
    refine ⟨(icoMatrix g).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightIcoSymmetry, icoSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (icoMatrix g).toEuclideanLin '' P.toC5.polyhedron.hull := by
      rwa [P.icoMatrix_image_hull g]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightIcoSymmetry, icoSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem RupertPose_rightIcoSymmetry_iff (p : MatrixPose) (g : IcoIndex) :
    RupertPose (p.rightIcoSymmetry g) P.toC5.polyhedron.hull ↔
      RupertPose p P.toC5.polyhedron.hull := by
  have houter : outerShadow (p.rightIcoSymmetry g) P.toC5.polyhedron.hull =
      outerShadow p P.toC5.polyhedron.hull := rfl
  simp only [RupertPose, P.innerShadow_rightIcoSymmetry, houter]

theorem matrixPoseWithOffset_ofPose_eq_rightIcoSymmetry
    (euler : Pose ℝ) (offset : ℝ²) (g : IcoIndex)
    (chart : ChartIndex) (x y z : ℝ)
    (hrelative :
      (euler.matrixPoseWithOffset offset).relativeRotation * icoMatrix g =
        chartMatrix chart * cayleyMatrix x y z) :
    (AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset =
      (euler.matrixPoseWithOffset offset).rightIcoSymmetry g := by
  let oldPose := euler.matrixPoseWithOffset offset
  let reduced := oldPose.rightIcoSymmetry g
  have hrelative' : reduced.relativeRotation =
      chartMatrix chart * cayleyMatrix x y z := by
    rw [MatrixPose.relativeRotation_rightIcoSymmetry]
    exact hrelative
  apply matrixPose_ext_val
  · calc
      ((AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset).innerRot.val =
          oldPose.outerRot.val * (chartMatrix chart * cayleyMatrix x y z) := by
            change (rotRM_mat euler.θ₂ euler.φ₂ 0 * chartMatrix chart) * cayleyMatrix x y z =
              rotRM_mat euler.θ₂ euler.φ₂ 0 * (chartMatrix chart * cayleyMatrix x y z)
            rw [Matrix.mul_assoc]
      _ = reduced.outerRot.val * reduced.relativeRotation := by
            rw [hrelative']
            rfl
      _ = reduced.innerRot.val :=
            Noperthedron.Atlas.MatrixPose.outer_mul_relativeRotation reduced
  · rfl
  · rfl

end IModel

end Noperthedron.SnubDodecahedron
