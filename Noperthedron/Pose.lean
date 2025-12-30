import Noperthedron.PoseClasses
import Noperthedron.Basic

structure Pose : Type where
  θ₁ : ℝ
  θ₂ : ℝ
  φ₁ : ℝ
  φ₂ : ℝ
  α : ℝ

noncomputable
instance : PoseLike Pose where
  inner vp := (rotRM vp.θ₁ vp.φ₁ vp.α).toAffineMap
  outer vp := (rotRM vp.θ₂ vp.φ₂ 0).toAffineMap

namespace Pose

-- Some convenience functions for doing rotations with dot notation
-- Maybe the rotations in basic could be inlined here? It depends on whether
-- we actually use them not in the context of a Pose.

noncomputable
def rotM₁ (p : Pose) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₁) (p.φ₁)
noncomputable
def rotM₂ (p : Pose) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₂) (p.φ₂)
noncomputable
def rotR (p : Pose) : ℝ² →L[ℝ] ℝ² := _root_.rotR (p.α)
noncomputable
def vecX₁ (p : Pose) : ℝ³ := vecX (p.θ₁) (p.φ₁)
noncomputable
def vecX₂ (p : Pose) : ℝ³ := vecX (p.θ₂) (p.φ₂)

noncomputable
def rotM₁θ (p : Pose) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θ (p : Pose) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₁φ (p : Pose) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂φ (p : Pose) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₂) (p.φ₂)
noncomputable
def rotR' (p : Pose) : ℝ² →L[ℝ] ℝ² := _root_.rotR' (p.α)

noncomputable
def inner (p : Pose) : ℝ³ →ᵃ[ℝ] ℝ² := innerProj p
noncomputable
def outer (p : Pose) : ℝ³ →ᵃ[ℝ] ℝ² := outerProj p

inductive equiv (p1 p2 : Pose) : Prop where
  | on_the_nose : p1.inner = p2.inner ∧ p1.outer = p2.outer → equiv p1 p2
  | off_by_neg : p1.inner = -p2.inner ∧ p1.outer = -p2.outer → equiv p1 p2

def innerParams (p : Pose) : ℝ³ := WithLp.toLp 2 ![p.α, p.θ₁, p.φ₁]

def outerParams (p : Pose) : ℝ² := WithLp.toLp 2 ![p.θ₂, p.φ₂]

lemma p_outer_eq_outer_shadow (p : Pose) (S : Set ℝ³) : p.outer '' S  = outerShadow p S := by
  simp only [Pose.outer, outerProj, outerShadow]
  ext v
  simp

lemma proj_rm_eq_m (θ φ : ℝ) (v : ℝ³) :
    proj_xyL (rotRM θ φ 0 v) = rotM θ φ v := by
  ext i
  simp [proj_xyL, rotRM, rotM, Matrix.vecHead, Matrix.vecTail, rotM_mat]
  fin_cases i <;> {
    simp only [Fin.isValue, Fin.zero_eta, Fin.isValue, Fin.mk_one,
               Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    try ring_nf
  }

lemma outer_eq_m2 (p : Pose) (v : ℝ³) : p.outer v = p.rotM₂ v :=
  proj_rm_eq_m p.θ₂ p.φ₂ v

/--
If we have a convex polyhedron with p being a pose witness of the
rupert property, then in particular every vertex in the "inner"
transformation lies in the convex hull of the vertices under the
"outer" transformation.
-/
theorem is_rupert_imp_inner_in_outer (p : Pose)
    (poly : Finset ℝ³)
    (h_rupert : RupertPose p (convexHull ℝ poly)) (v : ℝ³) (hv : v ∈ poly) :
     p.inner v ∈ convexHull ℝ (p.outer '' poly) := by
  simp only [RupertPose] at h_rupert
  grw [← subset_closure, interior_subset] at h_rupert
  simp only [Pose.inner]
  have : v ∈ convexHull ℝ poly := by rw [mem_convexHull_iff]; intro _ a _; exact a hv
  rw [← AffineMap.image_convexHull p.outer poly, p_outer_eq_outer_shadow]
  refine h_rupert ?_
  simp only [innerShadow, Set.mem_setOf_eq, innerProj]
  use v
  simpa

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

example : (s ⊆ closure s) := by exact subset_closure

lemma inner_shadow_eq_RM (p : Pose) (S : Set ℝ³) :
    innerShadow p S = (p.rotR ∘L p.rotM₁) '' S := by
  sorry

lemma outer_shadow_eq_M (p : Pose) (S : Set ℝ³) :
    outerShadow p S = p.rotM₂ '' S := by
  sorry

lemma poselike_inner_eq_proj_inner (p : Pose) :
    proj_xyL ∘ PoseLike.inner p = p.inner := by
  ext v i; fin_cases i <;>
    simp [Matrix.vecHead, PoseLike.inner, Pose.inner, innerProj]

lemma poselike_outer_eq_proj_outer (p : Pose) :
    proj_xyL ∘ PoseLike.outer p = p.outer := by
  ext v i; fin_cases i <;>
    simp [Matrix.vecHead, PoseLike.outer, Pose.outer, outerProj]

lemma equiv_rupert_imp_rupert {p1 p2 : Pose} {S : Set ℝ³} (e : equiv p1 p2) (r : RupertPose p1 S) :
    RupertPose p2 S := by
  match e with
  | .on_the_nose e =>
    simp only [RupertPose, innerShadow, outerShadow]
    obtain ⟨e_inner, e_outer⟩ := e
    calc
      closure ((proj_xyL ∘ PoseLike.inner p2) '' S)
      _ = closure (p2.inner '' S) := by rw [poselike_inner_eq_proj_inner p2]
      _ = closure (p1.inner '' S) := by rw [e_inner]
      _ ⊆ interior (p1.outer '' S) := r
      _ = interior (p2.outer '' S) := by rw [e_outer]
      _ = interior ((proj_xyL ∘ PoseLike.outer p2) '' S) := by rw [poselike_outer_eq_proj_outer p2]
  | .off_by_neg e =>
    simp only [RupertPose, innerShadow, outerShadow]
    obtain ⟨e_inner, e_outer⟩ := e
    calc
      closure ((proj_xyL ∘ PoseLike.inner p2) '' S)
      _ = closure (p2.inner '' S) := by rw [poselike_inner_eq_proj_inner p2]
      _ = closure (-p1.inner '' S) := by
        rw [e_inner]; simp only [AffineMap.coe_neg, Pi.neg_apply];
        congr; ext; simp only [Set.mem_neg, Set.mem_image, neg_inj]
      _ = -closure (p1.inner '' S) := Eq.symm (neg_closure (p1.inner '' S))
      _ ⊆ -(interior (p1.outer '' S)) := by rw [Set.neg_subset_neg]; exact r
      _ = interior (-(p1.outer '' S)) := (Homeomorph.neg ℝ²).preimage_interior (p1.outer '' S)
      _ = interior (-(-p2.outer) '' S) := by rw [e_outer]
      _ = interior (p2.outer '' S) := by congr; ext; simp
      _ = interior ((proj_xyL ∘ PoseLike.outer p2) '' S) := by rw [poselike_outer_eq_proj_outer p2]

lemma matrix_eq_imp_pose_equiv {p q : Pose} (re : p.rotR = q.rotR)
    (rm1 : p.rotM₁ = q.rotM₁) (rm2 : p.rotM₂ = q.rotM₂) : equiv p q := by
  refine equiv.on_the_nose ?_
  constructor
  · simp only [inner, innerProj, PoseLike.inner]
    ext1 v
    simp only [AffineMap.coe_comp,
      LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]
    change (proj_xyL ∘ rotRM p.θ₁ p.φ₁ p.α) v = (proj_xyL ∘ rotRM q.θ₁ q.φ₁ q.α) v
    rw [projxy_rotRM_eq_rotprojRM, projxy_rotRM_eq_rotprojRM]
    simp only [rotprojRM]
    change (p.rotR ∘ p.rotM₁) v = (q.rotR ∘ q.rotM₁) v
    rw [re, rm1]
  · simp only [outer, outerProj, PoseLike.outer]
    ext1 v
    simp only [AffineMap.coe_comp,
      LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]
    change (proj_xyL ∘ rotRM p.θ₂ p.φ₂ 0) v = (proj_xyL ∘ rotRM q.θ₂ q.φ₂ 0) v
    rw [projxy_rotRM_eq_rotprojRM, projxy_rotRM_eq_rotprojRM]
    simp only [rotprojRM, AddChar.map_zero_eq_one]
    change (p.rotM₂) v = (q.rotM₂) v
    rw [rm2]

lemma matrix_neg_imp_pose_equiv {p q : Pose} (re : p.rotR = q.rotR)
    (rm1 : p.rotM₁ = -q.rotM₁) (rm2 : p.rotM₂ = -q.rotM₂) : equiv p q := by
  refine equiv.off_by_neg ?_
  constructor
  · simp only [inner, innerProj, PoseLike.inner]
    ext1 v
    simp only [AffineMap.coe_comp,
      LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]
    change (proj_xyL ∘ rotRM p.θ₁ p.φ₁ p.α) v = (-proj_xyL ∘ rotRM q.θ₁ q.φ₁ q.α) v
    rw [projxy_rotRM_eq_rotprojRM, projxy_rotRM_eq_rotprojRM]
    simp only [rotprojRM]
    change (p.rotR ∘ p.rotM₁) v = (-q.rotR ∘ q.rotM₁) v
    rw [re, rm1]
    simp
  · simp only [outer, outerProj, PoseLike.outer]
    ext1 v
    simp only [AffineMap.coe_comp,
      LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]
    change (proj_xyL ∘ rotRM p.θ₂ p.φ₂ 0) v = (-proj_xyL ∘ rotRM q.θ₂ q.φ₂ 0) v
    rw [projxy_rotRM_eq_rotprojRM, projxy_rotRM_eq_rotprojRM]
    simp only [rotprojRM, AddChar.map_zero_eq_one]
    change (p.rotM₂) v = (-q.rotM₂) v
    rw [rm2]

end Pose
