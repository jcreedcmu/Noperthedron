module

public import Noperthedron.CommonCenter
public import Noperthedron.Vertices.Exact
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

/-!
# Shadows, Rupert pairs and the separation criterion

`shadow R` is the projection of the Noperthedron under the matrix `R`. A Rupert pair
`(Ro, Ri)` has the inner shadow inside the interior of the outer one.
We reduce `IsRupert exactVerts` to the existence of a Rupert pair of rotations (the offset can
be dropped because both shadows are centrally symmetric), and prove the only non-Rupert
criterion the checker uses: an inner vertex that no outer vertex beats in some direction
`w ≠ 0`.
-/

namespace Cayley

open Noperthedron
open scoped Matrix RealInnerProductSpace

/-- `x ↦ π (R x)`, the projection to the screen after applying `R`. -/
noncomputable def screen (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ³ →L[ℝ] ℝ² :=
  proj_xyL ∘L R.toEuclideanLin.toContinuousLinearMap

/-- The shadow of the Noperthedron under `R`. -/
noncomputable def shadow (R : Matrix (Fin 3) (Fin 3) ℝ) : Set ℝ² := screen R '' exactHull

/-- A Rupert passage with outer rotation `Ro` and inner rotation `Ri` (offset zero). The inner
shadow is compact, so there is no need to take its closure. -/
def RupPair (Ro Ri : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  shadow Ri ⊆ interior (shadow Ro)

theorem screen_apply (R : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ³) :
    screen R x = !₂[(R *ᵥ x.ofLp) 0, (R *ᵥ x.ofLp) 1] := by
  ext i
  fin_cases i <;>
    simp [screen, proj_xyL, proj_xy_mat, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three]

theorem screen_mul (L R : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ³) :
    screen (L * R) x = screen L (R.toEuclideanLin x) := by
  simp [screen, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- The offset of a Rupert passage of the Noperthedron can be dropped: both shadows are
centrally symmetric and the outer one is convex. -/
theorem exists_rupPair (h : IsRupert exactVerts) :
    ∃ Ro ∈ SO3, ∃ Ri ∈ SO3, RupPair Ro Ri := by
  obtain ⟨Ri, hRi, o, Ro, hRo, h⟩ := h
  refine ⟨Ro, hRo, Ri, hRi, ?_⟩
  have hsym (R) : PointSym (shadow R) :=
    continuousLinearMap_preserves_point_sym (screen R) exactHull_pointSym
  have hconv : Convex ℝ (shadow Ro) :=
    (convex_convexHull ℝ _).linear_image (screen Ro : ℝ³ →ₗ[ℝ] ℝ²)
  refine common_center (hsym Ri) (interior_preserves_point_sym (hsym Ro)) hconv.interior o ?_
  simpa [shadow, screen, Set.image, proj_xy_eq_proj_xyL, add_comm] using h

/-- The linear functional `x ↦ w₀ x₀ + w₁ x₁` on the first two coordinates. -/
def lin (w0 w1 : ℝ) (x : Fin 3 → ℝ) : ℝ := w0 * x 0 + w1 * x 1

theorem exactVertex_mem_hull (S : VertexIndex) : exactVertex S ∈ exactHull := by
  apply subset_convexHull
  simp [exactVerts]

/-- The separation criterion: a nonzero linear functional on the screen cannot attain its
maximum over the outer shadow at an interior point. -/
theorem not_rupPair_of_sep (Ro Ri : Matrix (Fin 3) (Fin 3) ℝ) (S : VertexIndex)
    (w0 w1 : ℝ) (hw : w0 ≠ 0 ∨ w1 ≠ 0)
    (h : ∀ T : VertexIndex,
      lin w0 w1 (Ro *ᵥ (exactVertex T).ofLp) ≤ lin w0 w1 (Ri *ᵥ (exactVertex S).ofLp)) :
    ¬ RupPair Ro Ri := by
  intro hR
  set f : ℝ² →L[ℝ] ℝ := innerSL ℝ !₂[w0, w1]
  have hf (R : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ³) : f (screen R x) = lin w0 w1 (R *ᵥ x.ofLp) := by
    simp [f, screen_apply, lin, inner, Fin.sum_univ_two, mul_comm]
  have hf0 : f ≠ 0 := by
    rw [Ne, ← map_zero (innerSL ℝ (E := ℝ²)), innerSL_inj]
    intro h0
    have h1 := congrArg (· 0) h0
    have h2 := congrArg (· 1) h0
    simp at h1 h2
    tauto
  set c := lin w0 w1 (Ri *ᵥ (exactVertex S).ofLp)
  -- the functional is at most `c` on the outer shadow
  have hhalf : shadow Ro ⊆ f ⁻¹' Set.Iic c := by
    rw [shadow, Set.image_subset_iff]
    refine convexHull_min ?_ ((convex_Iic c).is_linear_preimage (f ∘L screen Ro).isLinear)
    intro x hx
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hx
    exact (hf Ro _).trans_le (h T)
  -- so it is less than `c` on the interior
  have hint : f '' interior (shadow Ro) ⊆ Set.Iio c := by
    rw [← interior_Iic]
    exact interior_maximal (Set.image_subset_iff.2 (interior_subset.trans hhalf))
      (f.isOpenMap_of_ne_zero hf0 _ isOpen_interior)
  have hq : screen Ri (exactVertex S) ∈ shadow Ri := ⟨_, exactVertex_mem_hull S, rfl⟩
  exact lt_irrefl c ((hf Ri _).symm.trans_lt (hint ⟨_, hR hq, rfl⟩))

end Cayley

end
