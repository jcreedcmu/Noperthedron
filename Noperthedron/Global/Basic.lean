module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Noperthedron.PoseInterval

@[expose] public section


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
  rw [fderiv_const_smul hf, smul_apply, smul_eq_mul]

/-- Partial derivative of f/c equals (partial of f)/c -/
lemma nth_partial_div_const {n : ℕ} (i : Fin n) (f : E n → ℝ) (c : ℝ) (x : E n)
    (hf : DifferentiableAt ℝ f x) :
    nth_partial i (fun y => f y / c) x = nth_partial i f x / c := by
  simp only [div_eq_mul_inv, nth_partial, fderiv_mul_const hf, smul_apply,
    smul_eq_mul, mul_comm]

lemma nth_partial_nth_partial_div_const {n : ℕ} (i j : Fin n) (f : E n → ℝ) (c : ℝ) (x : E n)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ (nth_partial i f)) :
    nth_partial j (nth_partial i (fun y => f y / c)) x =
      nth_partial j (nth_partial i f) x / c := by
  rw [funext fun z => nth_partial_div_const i f c z (hf z)]
  exact nth_partial_div_const j (nth_partial i f) c x (hg x)

lemma nth_partial_nth_partial_nth_partial_div_const {n : ℕ} (i j k : Fin n) (f : E n → ℝ)
    (c : ℝ) (x : E n) (hf : Differentiable ℝ f) (hg : Differentiable ℝ (nth_partial k f))
    (hh : Differentiable ℝ (nth_partial j (nth_partial k f))) :
    nth_partial i (nth_partial j (nth_partial k (fun y => f y / c))) x =
      nth_partial i (nth_partial j (nth_partial k f)) x / c := by
  rw [funext fun z => nth_partial_nth_partial_div_const k j f c z hf hg]
  exact nth_partial_div_const i (nth_partial j (nth_partial k f)) c x (hh x)

def third_partials_bounded {n : ℕ} (f : E n → ℝ) : Prop :=
  ∀ (x : E n) (i j k : Fin n), |nth_partial i (nth_partial j (nth_partial k f)) x| ≤ 1

end GlobalTheorem

end
