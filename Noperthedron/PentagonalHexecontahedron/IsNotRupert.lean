module

public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveSolutionTree
public import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet

@[expose] public section

/-!
# The non-Rupert conclusion from valid tables

This file contains the small, certificate-independent bridge from four valid
Cayley-chart tables to the usual vertex-set formulation of the Rupert
property.
-/

open scoped Matrix

namespace Noperthedron.PentagonalHexecontahedron

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

/-- Valid exclusion tables for all four Cayley charts prove that no
icosahedral model (`IModel`: the snub dodecahedron and every I-orbit near
its rational model) is Rupert. -/
theorem not_rupert_of_valid_tables (Q : IModel)
    (table : ChartIndex → AtlasProjectiveSolutionTree.Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) (hcover : WedgeCover.coverValid = true) :
    ¬ IsRupert Q.toC5.verts := by
  intro hrupert
  have hset : IsRupertSet (convexHull ℝ Q.toC5.verts) :=
    (rupert_iff_rupert_set Q.toC5.verts).mp hrupert
  rw [← Q.toC5.polyhedron_hull] at hset
  exact no_matrixPose_of_valid_tables Q table hchart hvalid hcover
    (rupert_set_implies_matrix_pose hset)

end Noperthedron.PentagonalHexecontahedron

end
