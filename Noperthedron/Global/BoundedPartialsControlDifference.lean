import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Noperthedron.Nopert
import Noperthedron.PoseInterval
import Noperthedron.Global.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/- [SY25] Lemma 20 -/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

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

private noncomputable
def interpolator {n : ℕ} (x y : E n) (t : ℝ) : E n :=
  (1 - t) • x + t • y

private noncomputable
def interpolator' {n : ℕ} (x y : E n) : ℝ →L[ℝ] E n :=
  ContinuousLinearMap.toSpanSingleton ℝ (y - x)

private noncomputable
def interpolator_has_deriv {n : ℕ} (x y : E n) (t : ℝ) :
    HasFDerivAt (interpolator x y) (interpolator' x y) t := by
  unfold interpolator'
  rw [← hasDerivAt_iff_hasFDerivAt]
  unfold interpolator
  -- I don't really like this proof, I'd prefer something that more incrementally
  -- "discovers" the derivative of interpolator instead of building it all up and then
  -- `convert`ing it to the desired form.
  convert ((hasDerivAt_id t).const_sub 1).smul_const x |>.add ((hasDerivAt_id t).smul_const y) using 1
  ext i
  simp only [PiLp.sub_apply, neg_smul, one_smul, PiLp.add_apply, PiLp.neg_apply]
  ring_nf

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

private
lemma interpolated_deriv2_bound {n : ℕ} (x y : E n) {f : E n → ℝ}
    (mpb : mixed_partials_bounded f) {ε : ℝ} (hε : 0 < ε) (hdiff : (i : Fin n) → |x i - y i| ≤ ε)
    (t : ℝ) :
    |interpolated_deriv2 x y f t| ≤ n^2 * ε^2 := by
  calc |interpolated_deriv2 x y f t|
  _ ≤ ∑ i, |∑ j, (y i - x i) * (y j - x j) * nth_partial i (nth_partial j f) ((1 - t) • x + t • y)| := by
    apply Finset.abs_sum_le_sum_abs
  _ ≤ ∑ i, ∑ j, |(y i - x i) * (y j - x j) * nth_partial i (nth_partial j f) ((1 - t) • x + t • y)| := by
    refine Finset.sum_le_sum ?_; intro i hi;
    apply Finset.abs_sum_le_sum_abs
  _ = ∑ i, ∑ j, |(y i - x i)| * |(y j - x j)| * |nth_partial i (nth_partial j f) ((1 - t) • x + t • y)| := by
    conv => enter [1, 2, i, 2, j]; repeat rw [abs_mul];
  _ ≤ ∑ i, ∑ j, ε * ε * 1 := by
    refine Finset.sum_le_sum ?_; intro i hi;
    refine Finset.sum_le_sum ?_; intro j hj;
    rw [abs_sub_comm]; grw [hdiff i]
    rw [abs_sub_comm]; grw [hdiff j]
    unfold mixed_partials_bounded at mpb; grw [mpb]
  _ = n^2 * ε^2 := by
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf

lemma c2_imp_partials_differentiable {n : ℕ} {f : E n → ℝ} {i : Fin n} (fc : ContDiff ℝ 2 f) :
      Differentiable ℝ (nth_partial i f) := by
  have h_deriv : Differentiable ℝ (fderiv ℝ f) :=
    ContDiff.differentiable (n := 1) (by fun_prop) one_ne_zero
  exact h_deriv.clm_apply (differentiable_const _)

lemma c2_imp_partials_c1 {n : ℕ} {f : E n → ℝ} {j : Fin n} (fc : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (nth_partial j f) := by
  (apply ContDiff.fderiv_apply <;> try fun_prop); norm_num

lemma c2_imp_mixed_partials_continuous {n : ℕ} {f : E n → ℝ} {i j : Fin n} (fc : ContDiff ℝ 2 f) :
      Continuous (nth_partial i (nth_partial j f)) := by
  have h1 : ContDiff ℝ 1 (nth_partial j f) := c2_imp_partials_c1 fc
  have h0 : ContDiff ℝ 0 (nth_partial i (nth_partial j f)) := by
    (apply ContDiff.fderiv_apply <;> try fun_prop); norm_num
  exact h0.continuous

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

open ContinuousLinearMap in
def interpolated_has_deriv2 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (interpolated_deriv x y f) (interpolated_deriv2 x y f t) t := by
  unfold interpolated_deriv interpolated_deriv2
  rw [hasDerivAt_iff_hasFDerivAt]
  have hd (i : Fin n) : HasDerivAt (fun t => nth_partial i f (interpolator x y t))
      (∑ j, (y j - x j) * nth_partial j (nth_partial i f) (interpolator x y t)) t := by
    convert HasFDerivAt.comp_hasDerivAt t (c2_imp_partials_c1 fc |>.differentiable_one _ |>.hasFDerivAt)
      (interpolator_has_deriv x y t)
    rw [nth_partial_def]
    rfl
  convert HasFDerivAt.sum fun i _ => (HasDerivAt.hasFDerivAt (HasDerivAt.const_mul (y i - x i) (hd i)))
  all_goals try unfold interpolator
  · rw [Finset.sum_fn]
  · ext; simp only [toSpanSingleton_apply, smul_eq_mul, Finset.mul_sum, one_mul, coe_sum', Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring_nf

def deriv_interpolated {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) :
    deriv (interpolated x y f) = interpolated_deriv x y f := by
  ext t
  exact (interpolated_has_deriv x y f fc t).deriv

def deriv_interpolated2 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) :
    deriv (interpolated_deriv x y f) = interpolated_deriv2 x y f := by
  ext t
  exact (interpolated_has_deriv2 x y f fc t).deriv

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
    (mpb : mixed_partials_bounded f) :
    |f x - f y| ≤ ε * ∑ i, |nth_partial i f x| + (n^2 / 2) * ε^2 := by
  let g₀ := interpolator x y
  let g := interpolated x y f

  let g' := interpolated_deriv x y f
  let g'' := interpolated_deriv2 x y f

  have f_diff : Differentiable ℝ f := fc.differentiable (by norm_num)
  have g₀_diff : Differentiable ℝ g₀ := Differentiable.interpolator x y
  have g_diff : Differentiable ℝ g := Differentiable.interpolated x y f fc
  have g'_diff : Differentiable ℝ g' := differentiable_deriv_interpolated x y f fc
  have g'_cont : Continuous g' := g'_diff.continuous
  have g''_cont : Continuous g'' := continuous_deriv_interpolated2 x y f fc

  have deriv_g_eq_g' : deriv g = g' := by
    unfold g g'; exact deriv_interpolated x y f fc
  have deriv_g'_eq_g'' : deriv g' = g'' := by
    unfold g' g''; exact deriv_interpolated2 x y f fc

  have int_g'_eq_sub (t : ℝ) : (∫ (s : ℝ) in 0..t, g' s) = g t - g 0 := by
    exact intervalIntegral.integral_deriv_eq_sub' g deriv_g_eq_g' (by fun_prop) (by fun_prop)

  have int_g''_eq_sub (t : ℝ) : (∫ (s : ℝ) in 0..t, g'' s) = g' t - g' 0 := by
    exact intervalIntegral.integral_deriv_eq_sub' g' deriv_g'_eq_g'' (by fun_prop) (by fun_prop)

  -- "and observe that"
  have hobs := by calc g 1 - g 0
      _ = ∫ (t : ℝ) in 0..1, g' t := by rw [int_g'_eq_sub]
      _ = ∫ (t : ℝ) in 0..1, g' 0 + ∫ (s : ℝ) in 0..t, g'' s := by
        conv => enter [2, 1, t]; rw [int_g''_eq_sub]; simp
      _ = (∫ (t : ℝ) in 0..1, g' 0) + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s := by
        rw [intervalIntegral.integral_add]
        · exact intervalIntegrable_const
        · conv => enter [1, t]; rw [int_g''_eq_sub t]
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = g' 0 + ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, g'' s := by
        rw [intervalIntegral.integral_const]; simp

  --- "thus at t = 0 we find..."
  have bound1 : |g' 0| ≤ ε * ∑ i, |nth_partial i f x|  := by
    calc |g' 0|
    _ = |∑ i, (y i - x i) * nth_partial i f x| := by simp [g', interpolated_deriv]
    _ ≤ ∑ i, |(y i - x i) * nth_partial i f x| := by apply Finset.abs_sum_le_sum_abs
    _ = ∑ i, |(y i - x i)| * |nth_partial i f x| := by
      conv => enter [1, 2, i]; rw [abs_mul]
    _ = ∑ i, |(x i - y i)| * |nth_partial i f x| := by
      conv => enter [1, 2, i, 1]; rw [abs_sub_comm]
    _ ≤ ∑ i, ε * |nth_partial i f x| := by
      refine Finset.sum_le_sum ?_; intro i hi; grw [hdiff i]
    _ = ε * ∑ i, |nth_partial i f x| := by rw [Finset.mul_sum]

  -- "For the second derivative of g(t) we also get with the chain rule"
  have abs_int_le_int_abs {t : ℝ} (ht : 0 ≤ t) :
      |∫ (s : ℝ) in 0..t, g'' s| ≤ ∫ (s : ℝ) in 0..t, |g'' s| :=
    intervalIntegral.abs_integral_le_integral_abs ht

  have int_abs_int_le_int_int_abs : ∫ (t : ℝ) in 0..1, |∫ (s : ℝ) in 0..t, g'' s|
      ≤ ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, |g'' s| := by
    refine intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_
    · norm_num
    · exact Continuous.intervalIntegrable (by fun_prop) 0 1
    · exact Continuous.intervalIntegrable (by fun_prop) 0 1
    · intro t ⟨ht₁, ht₂⟩
      exact intervalIntegral.abs_integral_le_integral_abs ht₁

  have bound2 : ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, |g'' s| ≤ (n^2 / 2) * ε^2 := by
    suffices h : ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, |g'' s| ≤
        ∫ (t : ℝ) in 0..1, ∫ (s : ℝ) in 0..t, n^2 * ε^2 by
      grw [h]
      refine le_of_eq ?_
      simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero,
        smul_eq_mul, intervalIntegral.integral_mul_const, integral_id, one_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_div]
      ring_nf
    have : ∀ t ∈ Set.Icc 0 1, ∫ (s : ℝ) in 0..t, |g'' s| ≤ ∫ (s : ℝ) in 0..t, n^2 * ε^2 := by
      intro t ⟨ht, _⟩
      refine intervalIntegral.integral_mono ht ?_ ?_ (interpolated_deriv2_bound x y mpb hε hdiff) <;>
      · exact Continuous.intervalIntegrable (by fun_prop) 0 t
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ this <;>
      · exact Continuous.intervalIntegrable (by fun_prop) 0 1

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
