import Mathlib.Analysis.InnerProductSpace.PiL2
open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)


private lemma f_le_max {n : ℕ} {V : Finset (E n)} (w : E n → ℝ) (hw1 : ∀ y ∈ V, 0 ≤ w y)
      (f : E n →ₗ[ℝ] ℝ) :
  ↑(∑ x ∈ V, w x * f x) ≤ ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max := by
  have fx_le_fvmax (x : V) : f x ≤ (Finset.image f V).max := by
    refine Finset.le_max ?_
    simp only [Finset.mem_image]
    exact ⟨x, Finset.coe_mem x, rfl⟩
  push_cast
  refine Finset.sum_le_sum ?_
  intro x hx
  grw [fx_le_fvmax ⟨x, hx⟩]
  exact WithBot.coe_nonneg.mpr (hw1 x hx)

private lemma extract_constant {n : ℕ} {V : Finset (E n)} (w : E n → ℝ)
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max = ↑(∑ x ∈ V, w x) * (Finset.image (⇑f) V).max := by
  let ⟨S', hS'⟩ := convexHull_nonempty_iff.mp ⟨S, hs⟩
  let ⟨m, hm⟩ := Finset.max_of_mem (Finset.mem_image_of_mem f hS')
  rw [hm]
  suffices h : (WithBot.some (∑ x ∈ V, (w x) * m)) = WithBot.some ((∑ x ∈ V, w x) * m) by
    push_cast at h ⊢
    exact h
  refine congrArg WithBot.some ?_
  rw [← Finset.sum_mul]

theorem finset_hull_linear_max {n : ℕ} {V : Finset (E n)}
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ Finset.max (V.image f) := by
  have hs_orig := hs
  rw [Finset.convexHull_eq] at hs
  obtain ⟨w, hw1, hw2, hw3⟩ := hs
  calc
    ↑(f S) = ↑(f (∑ i ∈ V, w i • id i)) := by rw [← hw3, Finset.centerMass_eq_of_sum_1 V id hw2]
    _       = ↑(∑ x ∈ V, w x * f x) := by simp
    _       ≤ ↑(∑ x ∈ V, w x * ((Finset.image f V).max)) := f_le_max w hw1 f
    _       = ↑((∑ x ∈ V, w x) * (Finset.image f V).max) := extract_constant w S hs_orig f
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
