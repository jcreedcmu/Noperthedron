import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Noperthedron.Nopert
import Noperthedron.PoseInterval

open scoped RealInnerProductSpace

namespace GlobalTheorem

noncomputable
def nth_partial {n : ℕ} (i : Fin n) (f : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

def mixed_partials_bounded {n : ℕ} (f : E n → ℝ) (x : E n) : Prop :=
  ∀ (i j : Fin n), abs ((nth_partial i <| nth_partial j <| f) x) ≤ 1

end GlobalTheorem
