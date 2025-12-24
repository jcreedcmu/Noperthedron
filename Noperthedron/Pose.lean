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

def innerParams (p : Pose) : ℝ³ := WithLp.toLp 2 ![p.α, p.θ₁, p.φ₁]

def outerParams (p : Pose) : ℝ² := WithLp.toLp 2 ![p.θ₂, p.φ₂]

lemma p_outer_eq_outer_shadow (p : Pose) (S : Set ℝ³) : p.outer '' S  = outerShadow p S := by
  simp only [Pose.outer, outerProj, outerShadow]
  ext v
  simp

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

end Pose
