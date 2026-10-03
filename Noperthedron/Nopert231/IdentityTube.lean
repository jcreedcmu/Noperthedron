module

public import Noperthedron.Nopert231.AtlasProjectiveLocalViewTree
public import Noperthedron.Nopert231.WedgeCoverData
public import Noperthedron.Nopert231.AtlasProjectiveSolutionTree

@[expose] public section

/-!
# The identity tube from the per-triangle code tables

The identity-tube certificates come as one `Table` per code triangle (the
`code_C_tri_K.pack` files, in code order). Each valid table rules out
translated Rupert poses whose view lies in its triangle. `codeTriangles_cover`
says those triangles cover the base triangle T (given the natively checked
cover), so together the tables rule out every pose whose view lies in T and
whose tube is within the smallest table radius.
-/

namespace Noperthedron.Nopert231.IdentityTube

variable {P : C5Model}

open AtlasProjectiveView AtlasProjectiveLocalViewTree WedgeCover
open Noperthedron.Atlas.ProjectiveView

/-- The tables match the code triangles: table `t` is rooted at the upper
signed root, has triangle `codeTriangles[t]`, shares the symmetry index `s`,
and has radius at least `r`. -/
def TablesMatch (tables : ℕ → Table) (s : OrbitIndex) (r : ℚ) : Prop :=
  ∀ t (ht : t < codeTriangles.size),
    (tables t).root = 0 ∧ (tables t).triangle = codeTriangles[t] ∧
      (tables t).symmetryIndex = s ∧ r ≤ (tables t).r

instance (tables : ℕ → Table) (s : OrbitIndex) (r : ℚ) :
    Decidable (TablesMatch tables s r) := by
  unfold TablesMatch
  infer_instance

/-- Extend a validity prefix by one table (used by the native driver to
collect the per-table proofs). -/
theorem valid_prefix_succ {tables : ℕ → Table} {k : ℕ}
    (hk : ∀ t, t < k → (tables t).Valid) (hv : (tables k).Valid) :
    ∀ t, t < k + 1 → (tables t).Valid := by
  intro t ht
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
  · exact hk t h
  · exact h ▸ hv

/-- If every code triangle's table is valid (and the view cover checks), then
no pose with view in T is (translated) Rupert for any valid tube of symmetry `s` and radius at
most `r`. -/
theorem not_translated_rupert_of_tables (tables : ℕ → Table)
    (s : OrbitIndex) (r : ℚ) (hmatch : TablesMatch tables s r)
    (hvalid : ∀ t, t < codeTriangles.size → (tables t).Valid)
    (tube : Tube) (htubeSymmetry : tube.symmetryIndex = s)
    (htubeRadius : tube.r ≤ r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal)
    (hico : p.InIcoView) (hcover : coverValid = true) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      P.polyhedron.hull := by
  obtain ⟨hscale, hwedge⟩ := viewCone_mem_icoViewTriangle p hico
  rw [AtlasProjectiveSolutionTree.icoViewTriangle_eq_baseTriangle] at hwedge
  obtain ⟨t, tri, hget, hin⟩ := codeTriangles_cover hcover _ hwedge
  obtain ⟨ht, htri⟩ := Array.getElem?_eq_some_iff.mp hget
  obtain ⟨hroot, htriangle, hsym, hr⟩ := hmatch t ht
  apply (tables t).valid_imp_not_translated_rupert_in_triangle (hvalid t ht) tube
    (htubeSymmetry.trans hsym.symm) (htubeRadius.trans hr) htube hp
  · simpa [hroot] using hscale
  · simpa [hroot, htriangle, htri] using hin

end Noperthedron.Nopert231.IdentityTube

end
