import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Noperthedron.Nopert
import Noperthedron.PoseInterval
import Noperthedron.Global.Basic

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem bounded_partials_control_difference {n : ℕ} (f : E n → ℝ)
    (fc : ContDiff ℝ 2 f) (x y : E n)
    (ε : ℝ) (hε : ε > 0) (hdiff : (i : Fin n) → |x i - y i| ≤ ε)
    (mpb : mixed_partials_bounded f x) :
    |f x - f y| ≤ ε * ∑ i, |nth_partial i f x| + (n^2 / 2) * ε^2 := by
  let g₀ : ℝ → E n := fun t => (1 - t) • x + t • y
  let g := f ∘ g₀

  let g' (t : ℝ) : ℝ := ∑ i, (y i - x i) * nth_partial i f ((1 - t) • x + t • y)
  let g'' (t : ℝ) : ℝ := ∑ i, ∑ j, (y i - x i) * (y j - x j) * (nth_partial i <| nth_partial j f) ((1 - t) • x + t • y)

  have g₀_diff : Differentiable ℝ g₀ := by fun_prop
  have f_diff : Differentiable ℝ f := fc.differentiable (by norm_num)
  have g_diff : Differentiable ℝ g := by fun_prop
  have g'_diff : Differentiable ℝ g' := by sorry
  have g'_cont : Continuous g' := by fun_prop
  have g''_cont : Continuous g'' := by sorry

  have deriv_g_eq_g' : deriv g = g' := by
    ext x
    change fderiv ℝ g x 1 = g' x
    have fdc : fderiv ℝ (f ∘ g₀) x = (fderiv ℝ f (g₀ x)) ∘L (fderiv ℝ g₀ x) :=
      fderiv_comp x (by fun_prop) (by fun_prop)
    simp only [g, fdc,
      ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, one_smul]
    sorry

  have deriv_g'_eq_g'' : deriv g' = g'' := by
    sorry

  have int_g'_eq_sub (t : ℝ) : (∫ (s : ℝ) in 0..t, g' s) = g t - g 0 := by
    exact intervalIntegral.integral_deriv_eq_sub' g deriv_g_eq_g' (by fun_prop) (by fun_prop)

  have int_g''_eq_sub (t : ℝ) : (∫ (s : ℝ) in 0..t, g'' s) = g' t - g' 0 := by
    exact intervalIntegral.integral_deriv_eq_sub' g' deriv_g'_eq_g'' (by fun_prop) (by fun_prop)

  -- "and observe that"
  have hobs := by calc g 1 - g 0
      _ = ∫ (t : ℝ) in 0..1, g' t := by rw [int_g'_eq_sub]
      _ = ∫ (t : ℝ) in 0..1, g' 0 + ∫ (s : ℝ) in 0..t, g'' s := by
        conv => arg 2; arg 1; intro t; rw [int_g''_eq_sub]; simp
      _ = (∫ (t : ℝ) in 0..1, g' 0) + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s := by
        rw [intervalIntegral.integral_add]
        · exact intervalIntegrable_const
        · conv => arg 1; intro t; rw [int_g''_eq_sub t]
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = g' 0 + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s := by
        rw [intervalIntegral.integral_const]; simp

  --- "the chain rule imples that..."
  have bound1 : |g' 0| ≤ ε * ∑ i, |nth_partial i f x|  := by
    sorry

  -- "For the second derivative of g(t) we also get wit hthe chain rule"
  have bound2 : ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, |g'' s| ≤ (n^2 / 2) * ε^2 := by
    sorry

  have abs_int_le_int_abs {t : ℝ} (ht : 0 ≤ t) :
      |∫ (s : ℝ) in 0..t, g'' s| ≤ ∫ (s : ℝ) in 0..t, |g'' s| :=
    intervalIntegral.abs_integral_le_integral_abs ht

  -- This should be by monotonicity of integration applied to abs_int_le_int_abs
  have int_abs_int_le_int_int_abs : ∫ (t : ℝ) in 0..1, |∫ (s : ℝ) in 0..t, g'' s|
      ≤ ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, |g'' s| := by
    sorry

  -- "Altogether one obtains"
  calc |f x - f y|
  _ = |g 0 - g 1| := by
    rw [show g 0 = f x by simp[g, g₀]]
    rw [show g 1 = f y by simp[g, g₀]]
  _ = |g 1 - g 0| := by rw [abs_sub_comm]
  _ = |g' 0 + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s| := by rw [hobs]
  _ ≤ |g' 0| + |∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s| := abs_add_le _ _
  _ ≤ |g' 0| + ∫ (t : ℝ) in 0..1, |∫ (s : ℝ) in 0..t, g'' s| := by
    grw [intervalIntegral.abs_integral_le_integral_abs (by norm_num)]
  _ ≤ |g' 0| + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, |g'' s| := by
    grw [int_abs_int_le_int_int_abs]
  _ ≤ ε * ∑ i, |nth_partial i f x| + (n^2 / 2) * ε^2 := by grw[bound1, bound2]
