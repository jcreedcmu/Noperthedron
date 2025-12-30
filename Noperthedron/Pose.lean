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

def equiv (p1 p2 : Pose) : Prop :=
  p1.inner = p2.inner ∧ p1.outer = p2.outer

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

lemma poselike_inner_eq_proj_inner {v : ℝ³} (p : Pose) :
    proj_xyL (PoseLike.inner p v) = p.inner v := by
  ext i; fin_cases i <;>
    simp [Matrix.vecHead, PoseLike.inner, Pose.inner, innerProj]

lemma poselike_outer_eq_proj_outer {v : ℝ³} (p : Pose) :
    proj_xyL (PoseLike.outer p v) = p.outer v := by
  ext i; fin_cases i <;>
    simp [Matrix.vecHead, PoseLike.outer, Pose.outer, outerProj]

lemma equiv_rupert_imp_rupert {p1 p2 : Pose} {S : Set ℝ³} (e : equiv p1 p2) (r : RupertPose p1 S) :
    RupertPose p2 S := by
  simp only [RupertPose, innerShadow, outerShadow]
  obtain ⟨e_inner, e_outer⟩ := e
  conv =>
    lhs; arg 1; arg 1; intro x; arg 1; intro v
    rw [poselike_inner_eq_proj_inner p2, ← e_inner,
      ← poselike_inner_eq_proj_inner p1]
  conv =>
    rhs; arg 1; arg 1; intro x; arg 1; intro v
    rw [poselike_outer_eq_proj_outer p2, ← e_outer,
      ← poselike_outer_eq_proj_outer p1]
  exact r

end Pose
