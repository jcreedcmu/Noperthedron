module

public import Noperthedron.PentagonalHexecontahedron.HalfTurnReduce

@[expose] public section

/-!
# Atlas representatives in the half-turn cell (centrally symmetric models)

`IModel.exists_halfTurn_atlas_translated_pose`: for an icosahedral model whose
hull is centrally symmetric (the deltoidal hexecontahedron), every matrix pose
has an equivalent bounded atlas representative as in
`IModel.exists_ico_full_atlas_translated_pose` whose relative rotation also
lies in the half-turn cell of its view (`AtlasPose.InHalfTurnCell`): the
reduction maximizes the trace over the 120 candidates R g and H_u R g
(`exists_halfTurn_ico_reduction`), and the left half-turn preserves Rupert
poses of a centrally symmetric solid (`RupertPose_leftHalfTurn_iff`).
-/

namespace Noperthedron.PentagonalHexecontahedron

open scoped Matrix
open CayleyAtlas

/-- The half-turn cell condition carried by an atlas representative (view =
third row of the outer rotation). -/
def AtlasPose.InHalfTurnCell (p : AtlasPose ℝ) (chart : ChartIndex) : Prop :=
  Noperthedron.PentagonalHexecontahedron.InHalfTurnCell (fun k => rotRM_mat p.θ p.φ 0 2 k)
    (chartMatrix chart * cayleyMatrix p.x p.y p.z)

namespace IModel

/-- The model's hull is centrally symmetric (the deltoidal hexecontahedron). -/
def CentrallySymmetric (P : IModel) : Prop :=
  ∀ v ∈ P.toC5.polyhedron.hull, -v ∈ P.toC5.polyhedron.hull

/-- An atlas pose built from `euler` equals any pose with the same outer rotation, relative
rotation chart · cayley(x, y, z), and the given offset. -/
theorem matrixPoseWithOffset_ofPose_eq (euler : Pose ℝ) (reduced : MatrixPose)
    (houter : reduced.outerRot.val = rotRM_mat euler.θ₂ euler.φ₂ 0)
    (chart : ChartIndex) (x y z : ℝ)
    (hrelative : reduced.relativeRotation = chartMatrix chart * cayleyMatrix x y z) :
    (AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart reduced.innerOffset = reduced := by
  apply matrixPose_ext_val
  · calc
      ((AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart reduced.innerOffset).innerRot.val =
          rotRM_mat euler.θ₂ euler.φ₂ 0 * (chartMatrix chart * cayleyMatrix x y z) := by
            change (rotRM_mat euler.θ₂ euler.φ₂ 0 * chartMatrix chart) * cayleyMatrix x y z =
              rotRM_mat euler.θ₂ euler.φ₂ 0 * (chartMatrix chart * cayleyMatrix x y z)
            rw [Matrix.mul_assoc]
      _ = reduced.outerRot.val * reduced.relativeRotation := by rw [hrelative, houter]
      _ = reduced.innerRot.val := Noperthedron.Atlas.MatrixPose.outer_mul_relativeRotation reduced
  · exact houter.symm
  · rfl

/-- The reduction of one pose: same outer rotation, relative rotation in both cells, same
Rupert-ness (centrally symmetric hull). -/
theorem exists_halfTurn_reduced (P : IModel)
    (hsym : ∀ v ∈ P.toC5.polyhedron.hull, -v ∈ P.toC5.polyhedron.hull) (pose : MatrixPose) :
    ∃ reduced : MatrixPose, reduced.outerRot = pose.outerRot ∧
      InIcoFundamentalDomain reduced.relativeRotation ∧
      InHalfTurnCell pose.view reduced.relativeRotation ∧
      (RupertPose reduced P.toC5.polyhedron.hull ↔ RupertPose pose P.toC5.polyhedron.hull) := by
  have hu : ∑ k, pose.view k ^ 2 ≠ 0 := by rw [view_sq_sum]; norm_num
  obtain ⟨b, g, hfund, hcell⟩ := exists_halfTurn_ico_reduction pose.view hu pose.relativeRotation
  cases b
  · refine ⟨pose.rightIcoSymmetry g, rfl, ?_, ?_, P.RupertPose_rightIcoSymmetry_iff pose g⟩
    · rw [MatrixPose.relativeRotation_rightIcoSymmetry]
      simpa only [htCandidate, Bool.false_eq_true, if_false, Matrix.one_mul] using hfund
    · rw [MatrixPose.relativeRotation_rightIcoSymmetry]
      simpa only [htCandidate, Bool.false_eq_true, if_false, Matrix.one_mul] using hcell
  · have hrel : (pose.leftHalfTurn (icoSO3 g)).relativeRotation =
        htCandidate pose.view pose.relativeRotation true g := by
      rw [relativeRotation_leftHalfTurn]
      simp only [htCandidate, if_true]
      rfl
    refine ⟨pose.leftHalfTurn (icoSO3 g), rfl, ?_, ?_, ?_⟩
    · rw [hrel]; exact hfund
    · rw [hrel]; exact hcell
    · exact RupertPose_leftHalfTurn_iff pose (icoSO3 g) _ (P.icoMatrix_image_hull g) hsym

/-- Every matrix pose of a centrally symmetric icosahedral model has an equivalent bounded
atlas representative in the five-fold wedge, the view cone, the icosahedral cell, and the
half-turn cell. -/
theorem exists_halfTurn_atlas_translated_pose (P : IModel)
    (hsym : ∀ v ∈ P.toC5.polyhedron.hull, -v ∈ P.toC5.polyhedron.hull) (p : MatrixPose) :
    ∃ chart : CayleyAtlas.ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧ q.CayleyBounded ∧ q.InViewWedge ∧
      (q.InUpperView ∧ q.InIcoView) ∧ q.InIcoFundamentalDomain chart ∧ q.InHalfTurnCell chart ∧
      (RupertPose (q.matrixPoseWithOffset chart offset) P.toC5.polyhedron.hull ↔
        RupertPose p P.toC5.polyhedron.hull) := by
  obtain ⟨p1, hcone1, heq1⟩ := P.exists_viewCone_pose p
  obtain ⟨euler, offset, heuler, hview, hupper, hcone, heq⟩ :=
    exists_tight_pose_viewCone P.toC5 p1 hcone1
  obtain ⟨reduced, houter, hfund, hcell, hiff⟩ :=
    exists_halfTurn_reduced P hsym (euler.matrixPoseWithOffset offset)
  obtain ⟨chart, x, hx, y, hy, z, hz, hradius, hrelative⟩ :=
    CayleyAtlas.exists_bounded_chart_cayley reduced.relativeRotation
      (Noperthedron.Atlas.MatrixPose.relativeRotation_mem_SO3 reduced)
  have houter' : reduced.outerRot.val = rotRM_mat euler.θ₂ euler.φ₂ 0 := by rw [houter]; rfl
  have hmatrix : (AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart reduced.innerOffset = reduced :=
    matrixPoseWithOffset_ofPose_eq euler reduced houter' chart x y z hrelative
  refine ⟨chart, AtlasPose.ofPose euler x y z, reduced.innerOffset,
    AtlasPose.ofPose_mem_root euler x y z heuler.1 hx hy hz, hradius, ?_,
    ⟨?_, AtlasPose.inIcoView_ofPose euler x y z hcone⟩, ?_, ?_, ?_⟩
  · simpa [AtlasPose.InViewWedge, AtlasPose.ofPose, InViewWedge] using hview
  · simpa [AtlasPose.InUpperView, AtlasPose.ofPose] using hupper
  · show InIcoFundamentalDomain (chartMatrix chart * cayleyMatrix x y z)
    rw [← hrelative]; exact hfund
  · show InHalfTurnCell (fun k => rotRM_mat euler.θ₂ euler.φ₂ 0 2 k) (chartMatrix chart * cayleyMatrix x y z)
    rw [← hrelative, ← houter']
    have hv : (euler.matrixPoseWithOffset offset).view = fun k => reduced.outerRot.val 2 k := by
      rw [houter]; rfl
    rw [hv] at hcell
    exact hcell
  · rw [hmatrix, hiff, heq, heq1]

end IModel

/-! ### The half-turn cell at views given by a projective region -/

theorem halfTurnMat_smul (κ : ℝ) (hκ : κ ≠ 0) (u : Fin 3 → ℝ) : halfTurnMat (κ • u) = halfTurnMat u := by
  ext i j
  simp only [halfTurnMat, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [show ∑ k, (κ * u k) ^ 2 = κ ^ 2 * ∑ k, u k ^ 2 by rw [Finset.mul_sum]; congr 1; ext k; ring]
  by_cases hs : ∑ k, u k ^ 2 = 0
  · rw [hs]; simp
  · field_simp

theorem inHalfTurnCell_smul {u : Fin 3 → ℝ} {κ : ℝ} (hκ : κ ≠ 0) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (h : InHalfTurnCell (κ • u) R) : InHalfTurnCell u R := by
  intro g
  have := h g
  rwa [halfTurnMat_smul κ hκ] at this

/-- A pose whose normalized view lies in a projective triangle has view
viewScale · Σ w_c T_c, so its half-turn cell is the one at the triangle point. -/
theorem inHalfTurnCell_of_region {p : AtlasPose ℝ} {chart : ChartIndex} {root : Fin 8}
    {T : AtlasProjectiveView.Triangle ℚ}
    (hcell : p.InHalfTurnCell chart) (hscale : 1 ≤ AtlasProjectiveView.viewScale root p)
    {w : Fin 3 → ℝ} (hw : AtlasProjectiveView.normalizedView root p =
      Noperthedron.Atlas.ProjectiveView.affinePoint (Noperthedron.Atlas.ProjectiveView.toReal T) w) :
    InHalfTurnCell (AtlasHalfTurnPrune.viewOf T w) (chartMatrix chart * cayleyMatrix p.x p.y p.z) := by
  have hκ : AtlasProjectiveView.viewScale root p ≠ 0 := by linarith
  apply inHalfTurnCell_smul hκ
  have hview : AtlasProjectiveView.viewScale root p • AtlasHalfTurnPrune.viewOf T w =
      fun k => rotRM_mat p.θ p.φ 0 2 k := by
    funext k
    have hk := congrFun hw k
    simp only [AtlasProjectiveView.normalizedView] at hk
    rw [rotRM_mat_row2]
    simp only [Pi.smul_apply, smul_eq_mul, AtlasHalfTurnPrune.viewOf]
    have : (∑ c, w c * (T c k : ℝ)) =
        Noperthedron.Atlas.ProjectiveView.affinePoint (Noperthedron.Atlas.ProjectiveView.toReal T) w k := by
      simp [Noperthedron.Atlas.ProjectiveView.affinePoint, Noperthedron.Atlas.ProjectiveView.toReal]
    rw [this, ← hk, mul_div_cancel₀ _ hκ]
    fin_cases k <;> simp [eulerView, AtlasEdgeCertificate.viewVector]
  rw [hview]
  exact hcell

end Noperthedron.PentagonalHexecontahedron
