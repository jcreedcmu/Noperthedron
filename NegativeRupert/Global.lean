import Mathlib.Analysis.InnerProductSpace.PiL2
open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem finset_hull_linear_max {n : ℕ} {V : Finset (E n)}
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ Finset.max (V.image f) := by
  rw [Finset.convexHull_eq] at hs
  obtain ⟨w, hw1, hw2, hw3⟩ := hs
  have fx_le_fvmax (x : V) : f x ≤ (Finset.image f V).max := by
    refine Finset.le_max ?_
    simp only [Finset.mem_image]
    exact ⟨x, Finset.coe_mem x, rfl⟩

  have le_imp_sum_le  {b : WithBot ℝ} (hle : (x : V) → f x ≤ b) :
     ↑ (∑ x ∈ V, w x * f x) ≤ (∑ x ∈ V, w x * b) := by
    push_cast
    refine Finset.sum_le_sum ?_
    intro x hx
    grw [hle ⟨x, hx⟩]
    exact WithBot.coe_nonneg.mpr (hw1 x hx)

  calc
    ↑(f S) = ↑(f (∑ i ∈ V, w i • id i)) := by rw [← hw3, Finset.centerMass_eq_of_sum_1 V id hw2]
    _       = ↑(∑ x ∈ V, w x * f x) := by simp
    _       ≤ ↑(∑ x ∈ V, w x * ((Finset.image f V).max)) := le_imp_sum_le fx_le_fvmax
    _       = ↑((∑ x ∈ V, w x) * (Finset.image f V).max) := by sorry
    _       = (Finset.image f V).max := by rw [hw2]; simp

theorem fintype_hull_linear_max {n : ℕ} {ι : Type} [Fintype ι] (V : ι → E n)
    (S : E n) (hs : S ∈ convexHull ℝ (Set.range V)) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ Finset.max (Finset.univ.image (f ∘ V)) := by
  sorry

theorem hull_scalar_prod {n : ℕ} {ι : Type} [Fintype ι] (V : ι → E n)
    (S : E n) (hs : S ∈ convexHull ℝ (Set.range V)) (w : E n) :
    ⟪S, w⟫ ≤ Finset.max (Finset.univ.image (⟪V ·, w⟫)) := by
  sorry

end GlobalTheorem
