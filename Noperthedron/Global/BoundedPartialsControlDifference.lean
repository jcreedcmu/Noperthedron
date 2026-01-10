import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Noperthedron.Nopert
import Noperthedron.PoseInterval
import Noperthedron.Global.Basic

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private noncomputable
def interpolator {n : ℕ} (x y : E n) (t : ℝ) : E n :=
  (1 - t) • x + t • y

private noncomputable
def interpolator' {n : ℕ} (x y : E n) : ℝ →L[ℝ] E n :=
  ContinuousLinearMap.toSpanSingleton ℝ (y - x)

private noncomputable
def interpolator_has_deriv {n : ℕ} (x y : E n) (t : ℝ) :
    HasFDerivAt (interpolator x y) (interpolator' x y) t := by
  sorry

private noncomputable
def interpolated {n : ℕ} (x y : E n) (f : E n → ℝ) : ℝ → ℝ  :=
  f ∘ interpolator x y

private noncomputable
def Differentiable.interpolator {n : ℕ} (x y : E n) :
    Differentiable ℝ (interpolator x y)  := by
  unfold GlobalTheorem.interpolator
  fun_prop

private noncomputable
def Differentiable.interpolated {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) :
    Differentiable ℝ (interpolated x y f)  := by
  have := Differentiable.interpolator x y
  have := fc.differentiable (by norm_num)
  unfold GlobalTheorem.interpolated
  fun_prop

private noncomputable
def interpolated_deriv {n : ℕ} (x y : E n) (f : E n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (y i - x i) * nth_partial i f ((1 - t) • x + t • y)

private noncomputable
def interpolated_deriv2 {n : ℕ} (x y : E n) (f : E n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, (y i - x i) * (y j - x j) * (nth_partial i <| nth_partial j f) ((1 - t) • x + t • y)

lemma c2_imp_partials_differentiable {n : ℕ} {f : E n → ℝ} {i : Fin n} (fc : ContDiff ℝ 2 f) :
      Differentiable ℝ (nth_partial i f) := by
  sorry

lemma c2_imp_mixed_partials_continuous {n : ℕ} {f : E n → ℝ} {i j : Fin n} (fc : ContDiff ℝ 2 f) :
      Continuous (nth_partial i (nth_partial j f)) := by
  sorry

-- FIXME: the fact that I can't find exactly this lemma with loogle on "sum" and EuclideanSpace.single
-- makes me think there's probably some nearby lemma that uses different tools, maybe?
lemma vector_rep {n : ℕ} (v : E n) : v = ∑ x, v.ofLp x • EuclideanSpace.single x 1 := by
  ext i; simp [Finset.sum_apply, Pi.single_apply]

lemma nth_partial_def {n : ℕ} (f : E n → ℝ) (v w : E n) :
    fderiv ℝ f w v = ∑ i, v i * nth_partial i f w := by
  unfold nth_partial
  rw [show ∑ i, v.ofLp i * (fderiv ℝ f w) (EuclideanSpace.single i 1)
         = (fderiv ℝ f w) (∑ x, v.ofLp x • EuclideanSpace.single x 1)
      by simp]
  congr
  exact vector_rep v

open ContinuousLinearMap in
def interpolated_has_deriv {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (interpolated x y f) (interpolated_deriv x y f t) t := by
  unfold interpolated interpolated_deriv
  rw [hasDerivAt_iff_hasFDerivAt]
  have hfd : HasFDerivAt f (fderiv ℝ f (interpolator x y t)) (interpolator x y t) :=
    fc.differentiable (by norm_num) |>.differentiableAt.hasFDerivAt

  have : (toSpanSingleton ℝ (∑ i, (y.ofLp i - x.ofLp i) * nth_partial i f ((1 - t) • x + t • y)))
      = ((fderiv ℝ f (interpolator x y t)).comp (interpolator' x y)) := by
    unfold interpolator' interpolator
    ext
    simp only [toSpanSingleton_apply, smul_eq_mul, one_mul, coe_comp', Function.comp_apply,
      one_smul]
    rw [nth_partial_def f]
    congr
  rw [this]
  exact HasFDerivAt.comp t hfd (interpolator_has_deriv x y t)

def interpolated_has_deriv2 {n : ℕ} (x y : E n) (f : E n → ℝ) (t : ℝ) :
    HasDerivAt (interpolated_deriv x y f) (interpolated_deriv2 x y f t) t := by
  unfold interpolated_deriv interpolated_deriv2
  sorry

def deriv_interpolated {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f):
    deriv (interpolated x y f) = interpolated_deriv x y f := by
  ext t
  exact (interpolated_has_deriv x y f fc t).deriv

def deriv_interpolated2 {n : ℕ} (x y : E n) (f : E n → ℝ) :
    deriv (interpolated_deriv x y f) = interpolated_deriv2 x y f := by
  ext t
  exact (interpolated_has_deriv2 x y f t).deriv

def differentiable_deriv_interpolated {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) :
    Differentiable ℝ (interpolated_deriv x y f) := by
  unfold interpolated_deriv
  refine Differentiable.fun_sum ?_; intro i hi
  refine Differentiable.mul (by fun_prop) ?_
  change Differentiable ℝ ((fun v ↦ nth_partial i f v) ∘ (fun t ↦ (1 - t) • x + t • y))
  refine Differentiable.comp ?_ (by fun_prop)
  exact c2_imp_partials_differentiable fc

def continuous_deriv_interpolated2 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) :
    Continuous (interpolated_deriv2 x y f) := by
  unfold interpolated_deriv2
  refine continuous_finset_sum Finset.univ ?_; intro i hi
  refine continuous_finset_sum Finset.univ ?_; intro j hj
  refine Continuous.mul (by fun_prop) ?_
  change Continuous ((fun v ↦ nth_partial i (nth_partial j f) v) ∘ (fun t ↦ (1 - t) • x + t • y))
  refine Continuous.comp ?_ (by fun_prop)
  exact c2_imp_mixed_partials_continuous fc

theorem bounded_partials_control_difference {n : ℕ} (f : E n → ℝ)
    (fc : ContDiff ℝ 2 f) (x y : E n)
    (ε : ℝ) (hε : ε > 0) (hdiff : (i : Fin n) → |x i - y i| ≤ ε)
    (mpb : mixed_partials_bounded f x) :
    |f x - f y| ≤ ε * ∑ i, |nth_partial i f x| + (n^2 / 2) * ε^2 := by
  let g₀ := interpolator x y
  let g := interpolated x y f

  let g' := interpolated_deriv x y f
  let g'' := interpolated_deriv2 x y f

  have f_diff : Differentiable ℝ f := fc.differentiable (by norm_num)
  have g₀_diff : Differentiable ℝ g₀ := Differentiable.interpolator x y
  have g_diff : Differentiable ℝ g := Differentiable.interpolated x y f fc
  have g'_diff : Differentiable ℝ g' := differentiable_deriv_interpolated x y f fc
  have g'_cont : Continuous g' := by fun_prop
  have g''_cont : Continuous g'' := continuous_deriv_interpolated2 x y f fc

  have deriv_g_eq_g' : deriv g = g' := by
    unfold g g'; exact deriv_interpolated x y f fc
  have deriv_g'_eq_g'' : deriv g' = g'' := by
    unfold g' g''; exact deriv_interpolated2 x y f

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
    rw [show g 0 = f x by simp[g, interpolated, interpolator]]
    rw [show g 1 = f y by simp[g, interpolated, interpolator]]
  _ = |g 1 - g 0| := by rw [abs_sub_comm]
  _ = |g' 0 + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s| := by rw [hobs]
  _ ≤ |g' 0| + |∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s| := abs_add_le _ _
  _ ≤ |g' 0| + ∫ (t : ℝ) in 0..1, |∫ (s : ℝ) in 0..t, g'' s| := by
    grw [intervalIntegral.abs_integral_le_integral_abs (by norm_num)]
  _ ≤ |g' 0| + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, |g'' s| := by
    grw [int_abs_int_le_int_int_abs]
  _ ≤ ε * ∑ i, |nth_partial i f x| + (n^2 / 2) * ε^2 := by grw[bound1, bound2]
