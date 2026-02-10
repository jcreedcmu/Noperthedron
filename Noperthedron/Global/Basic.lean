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

/-- Partial derivative of a scalar multiple equals scalar times partial derivative -/
lemma nth_partial_const_smul {n : ℕ} (i : Fin n) (c : ℝ) (f : E n → ℝ) (x : E n)
    (hf : DifferentiableAt ℝ f x) :
    nth_partial i (c • f) x = c * nth_partial i f x := by
  simp only [nth_partial]
  rw [fderiv_const_smul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Partial derivative of f/c equals (partial of f)/c -/
lemma nth_partial_div_const {n : ℕ} (i : Fin n) (f : E n → ℝ) (c : ℝ) (x : E n)
    (hf : DifferentiableAt ℝ f x) :
    nth_partial i (fun y => f y / c) x = nth_partial i f x / c := by
  simp only [div_eq_mul_inv, nth_partial, fderiv_mul_const hf, ContinuousLinearMap.smul_apply,
    smul_eq_mul, mul_comm]

lemma nth_partial_nth_partial_div_const {n : ℕ} (i j : Fin n) (f : E n → ℝ) (c : ℝ) (x : E n)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ (nth_partial j f)) :
    nth_partial i (nth_partial j (fun y => f y / c)) x =
      nth_partial i (nth_partial j f) x / c := by
  rw [funext fun z => nth_partial_div_const j f c z (hf z)]
  exact nth_partial_div_const i (nth_partial j f) c x (hg x)

def mixed_partials_bounded {n : ℕ} (f : E n → ℝ) : Prop :=
  ∀ (x : E n) (i j : Fin n), abs ((nth_partial i <| nth_partial j <| f) x) ≤ 1

end GlobalTheorem
