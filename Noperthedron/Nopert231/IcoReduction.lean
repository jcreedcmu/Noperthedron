module

public import Noperthedron.Nopert231.AtlasIcoPrune
public import Noperthedron.Nopert231.IcoModel

@[expose] public section

/-!
# Reducing the relative rotation modulo I

For an `IModel` (whose hull every rotation of I preserves), composing the
inner copy with g ∈ I changes neither shadow, so the relative rotation can
be moved into the icosahedral max-trace cell (nopert229/notes/S.md §2.3,
reduction 1). `exists_ico_atlas_translated_pose` is
`AtlasFundamentalPrune.exists_fundamental_atlas_translated_pose` with that
cell in place of the fivefold one; the view reduction is unchanged.
-/

namespace Noperthedron.Nopert231

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
  Noperthedron.Nopert231.InIcoFundamentalDomain (chartMatrix chart * cayleyMatrix p.x p.y p.z)

theorem AtlasPose.InIcoFundamentalDomain.toFivefold {p : AtlasPose ℝ} {chart : ChartIndex}
    (h : p.InIcoFundamentalDomain chart) : p.InFivefoldFundamentalDomain chart :=
  Noperthedron.Nopert231.InIcoFundamentalDomain.toFivefold (R := chartMatrix chart * cayleyMatrix p.x p.y p.z) h

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

/-- Every matrix pose has an equivalent bounded atlas representative whose
relative rotation is in the icosahedral cell (and the view is reduced as for
#231). -/
theorem exists_ico_atlas_translated_pose (p : MatrixPose) :
    ∃ chart : ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧ q.CayleyBounded ∧ q.InViewWedge ∧
      q.InUpperView ∧ q.InIcoFundamentalDomain chart ∧
      (RupertPose (q.matrixPoseWithOffset chart offset) P.toC5.polyhedron.hull ↔
        RupertPose p P.toC5.polyhedron.hull) := by
  obtain ⟨euler, offset, heuler, hview, hupper, heq⟩ :=
    exists_upper_tight_translated_pose (P := P.toC5) p
  let oldPose := euler.matrixPoseWithOffset offset
  obtain ⟨g, hgfund⟩ := exists_mul_ico_inFundamentalDomain oldPose.relativeRotation
  let reduced := oldPose.rightIcoSymmetry g
  obtain ⟨chart, x, hx, y, hy, z, hz, hradius, hrelative⟩ :=
    exists_bounded_chart_cayley reduced.relativeRotation
      (Noperthedron.Atlas.MatrixPose.relativeRotation_mem_SO3 reduced)
  let q := AtlasPose.ofPose euler x y z
  have hq : q ∈ AtlasPose.rootInterval ℝ :=
    AtlasPose.ofPose_mem_root euler x y z heuler.1 hx hy hz
  have hmatrix : q.matrixPoseWithOffset chart offset = reduced := by
    apply matrixPoseWithOffset_ofPose_eq_rightIcoSymmetry
    rw [← MatrixPose.relativeRotation_rightIcoSymmetry]
    exact hrelative
  have hqfund : q.InIcoFundamentalDomain chart := by
    have h := AtlasPose.matrixPoseWithOffset_relativeRotation chart q offset
    rw [hmatrix, MatrixPose.relativeRotation_rightIcoSymmetry] at h
    rw [AtlasPose.InIcoFundamentalDomain, ← h]
    exact hgfund
  refine ⟨chart, q, offset, hq, hradius, ?_, ?_, hqfund, ?_⟩
  · simpa [q, AtlasPose.InViewWedge, AtlasPose.ofPose, InViewWedge] using hview
  · simpa [q, AtlasPose.InUpperView, AtlasPose.ofPose] using hupper
  · rw [hmatrix, P.RupertPose_rightIcoSymmetry_iff]
    exact heq

end IModel

end Noperthedron.Nopert231
