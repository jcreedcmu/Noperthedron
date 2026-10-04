module

public import Noperthedron.Nopert231.AtlasProjectiveSolutionTree
public import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet

@[expose] public section

/-!
# The public non-Rupert conclusion for Nopert #231

This file contains the small, certificate-independent bridge from four valid
Cayley-chart tables to the usual vertex-set formulation of the Rupert
property.
-/

open scoped Matrix

namespace Noperthedron.Nopert231

variable {P : C5Model}

open CayleyAtlas
open AtlasProjectiveSolutionTree

private lemma rupert_set_implies_matrix_pose {S : Set ℝ³}
    (h : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, innerSO3, offset, outer, outerSO3, hshadow⟩ := h
  let p : MatrixPose :=
    MatrixPose.mk ⟨inner, innerSO3⟩ ⟨outer, outerSO3⟩ offset
  refine ⟨p, ?_⟩
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  rw [p.inner_shadow_lemma, outerShadow]
  repeat rw [← proj_xy_eq_proj_xyL]
  exact hshadow

/-- Valid exclusion tables for all four Cayley charts prove that the model
`P` (any fivefold-symmetric polyhedron close to the rational vertices) is not
Rupert. -/
theorem not_rupert_of_valid_tables
    (table : ChartIndex → AtlasProjectiveSolutionTree.Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) :
    ¬ IsRupert P.verts := by
  intro hrupert
  have hset : IsRupertSet (convexHull ℝ P.verts) :=
    (rupert_iff_rupert_set P.verts).mp hrupert
  rw [← P.polyhedron_hull] at hset
  exact no_matrixPose_of_valid_tables table hchart hvalid
    (rupert_set_implies_matrix_pose hset)

end Noperthedron.Nopert231

end
