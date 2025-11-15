import Mathlib.Analysis.InnerProductSpace.PiL2
open scoped RealInnerProductSpace

namespace GlobalTheorem

noncomputable
def max_inner_prod {n : ℕ} {ι : Type} [Fintype ι] (V : ι → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) : WithBot ℝ :=
  Finset.univ.image (⟪V ·, w⟫) |>.max

theorem hull_scalar_prod {n : ℕ} {ι : Type} [Fintype ι] [Nonempty ι] (V : ι → EuclideanSpace ℝ (Fin n))
    (S : EuclideanSpace ℝ (Fin n)) (hs : S ∈ convexHull ℝ (Set.range V)) (w : EuclideanSpace ℝ (Fin n)) :
    ⟪S, w⟫ ≤ max_inner_prod V w := by
  sorry

end GlobalTheorem
