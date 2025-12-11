import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Int.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.StarOrdered

import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Cases
import Noperthedron.Lemma39
import Noperthedron.Basic

namespace RationalApprox

open scoped Nat -- for ! notation

noncomputable section

/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯$ up to and including the degree $2n-1$ term.
-/
def sin_psum (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯$ up to and including the degree $2n-2$ degree term.
-/
def cos_psum (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / (2 * i)!)

/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯ + x^{25}/25!$
-/
def sinℚ := sin_psum 13

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯ + x^{24}/24!$
-/
def cosℚ := cos_psum 13

/--
Frequently used constant for controlling the degree of approximation
of rational versions to real counterparts.
-/
def κ : ℝ := 1 / 10^10

def κApproxMat {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (A' : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ‖(A - A'.map (fun x => (↑x : ℝ))).toEuclideanLin.toContinuousLinearMap‖ ≤ κ

def κApproxPoint {m n : ℕ} (A A' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ‖(A - A').toEuclideanLin.toContinuousLinearMap‖ ≤ κ

end

section AristotleLemmas

theorem finset_sum_range_even_odd {n : ℕ} {f : ℕ → ℝ}
    : ∑ i ∈ Finset.range (2 * n + 1), f i =
      ∑ i ∈ Finset.range n, f (2 * i + 1) + ∑ i ∈ Finset.range (n + 1), f (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    nth_rw 2 [Finset.sum_range_succ, Finset.sum_range_succ]
    ring_nf

theorem taylorWithinEval_sin {n : ℕ} {x : ℝ} (hx' : 0 < x) :
    taylorWithinEval Real.sin (2 * n) (Set.Icc 0 x) 0 x =
       ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / ↑(2 * i + 1)!) := by
  have h_poly_eval : taylorWithinEval Real.sin (2 * n) (Set.Icc 0 x) 0 x =
       ∑ i ∈ Finset.range (2 * n + 1), (iteratedDeriv i Real.sin 0) * x ^ i / (i ! : ℝ) := by
    rw [taylor_within_apply]
    congr; ext i
    rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc hx') Real.contDiff_sin.contDiffAt (Set.left_mem_Icc.mpr hx'.le)]
    simp [field]
  rw [finset_sum_range_even_odd] at h_poly_eval
  rw [h_poly_eval]
  simp [mul_div_assoc]

/--
The error of the degree $2n$ Taylor polynomial for sine is bounded by $|x|^{2n+1}/(2n+1)!$.
-/
theorem sin_approx_aux (x : ℝ) (n : ℕ) :
    |Real.sin x - ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)| ≤
    |x| ^ (2 * n + 1) / (2 * n + 1)! := by
  rw [le_div_iff₀ (by positivity)]
  wlog hx : 0 < x with H
  · obtain rfl | hx := eq_or_lt_of_not_gt hx
    · simp
    · specialize H (-x) n (by linarith)
      rw [abs_neg] at H
      convert H using 1
      congr 1
      simp only [mul_comm, pow_add, pow_one, mul_assoc, div_eq_mul_inv, Real.sin_neg,
        even_two, Even.mul_left, Even.neg_pow, neg_mul, mul_neg, Finset.sum_neg_distrib,
        sub_neg_eq_add]
      grind

  have h_lagrange : ∀ x : ℝ, 0 < x →
      ∃ c ∈ Set.Icc 0 x,
        Real.sin x - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!) =
        (iteratedDeriv (2 * n + 1) Real.sin c) * x ^ (2 * n + 1) / (2 * n + 1)! := by
    intro x hx
    obtain ⟨c, hc₁, hc₂⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 2 * n) hx Real.contDiff_sin.contDiffOn
    use c
    refine ⟨⟨hc₁.1.le, hc₁.2.le⟩, ?_⟩
    simp only [taylorWithinEval_sin hx, sub_zero] at hc₂
    exact hc₂
  specialize h_lagrange x hx
  obtain ⟨w, -, h₂⟩ := h_lagrange
  simp only [h₂, Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_even_cos, Pi.mul_apply,
    Pi.pow_apply, Pi.neg_apply, Pi.ofNat_apply, ge_iff_le]
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, fieldLe]
  exact Real.abs_cos_le_one w

set_option maxHeartbeats 500000 in
/--
The difference between cos(x) and its Taylor polynomial of degree 2n-2 is bounded by |x|^(2n)/(2n)!.
-/
theorem Real.cos_approx_sum (x : ℝ) (n : ℕ) :
    |Real.cos x - ∑ i ∈ Finset.range n, (-1)^i * x^(2*i) / (2*i)!| ≤ |x|^(2*n) / (2*n)! := by
  induction n generalizing x with
  | zero => simpa using Real.abs_cos_le_one x
  | succ n ih =>
    -- Apply the induction hypothesis to rewrite the sum.
    have h_rewrite :
          |Real.cos x - ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * x ^ (2 * i) / (2 * i)!| =
          |∫ t in (0 : ℝ)..x, (Real.sin t - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * t ^ (2 * i + 1) /
           (2 * i + 1)!)| := by
      rw [intervalIntegral.integral_sub]
      · -- The integral of the series up to n terms is the same as the sum of the series up to n terms.
        simp only [Finset.sum_range_succ', pow_zero, mul_zero, mul_one, Nat.factorial_zero,
          Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, integral_sin, Real.cos_zero]
        have h_integral :
              ∫ x in (0 : ℝ)..x, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * i + 1)! =
              ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * x ^ (2 * i + 2) / (2 * i + 2)! := by
          rw [intervalIntegral.integral_finset_sum]
          · simp_all only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
              integral_pow, ne_eq, Nat.add_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
              one_ne_zero, and_false, and_self, not_false_eq_true, zero_pow, sub_zero, Nat.cast_add,
              Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
            field_simp
            exact Finset.sum_congr rfl fun _ _ => by push_cast [ Nat.factorial_succ ]; ring
          · aesop
        rw [h_integral]
        simp only [pow_succ', neg_mul, one_mul, Nat.mul_succ, div_eq_mul_inv, Finset.sum_neg_distrib]
        rw [← abs_neg]
        ring_nf
      · norm_num [Finset.sum_range_succ']
      · exact Continuous.intervalIntegrable ( by fun_prop ) _ _
    -- Apply the induction hypothesis to the integral.
    have h_ind : ∀ t ∈ Set.Icc (0 : ℝ) |x|,
        |Real.sin t - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * t ^ (2 * i + 1) / (2 * i + 1)!| ≤
        |t| ^ (2 * n + 1) / (2 * n + 1)! := by
      intro t ht
      have h_ind : |Real.sin t - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * t ^ (2 * i + 1) / (2 * i + 1)!| = |∫ u in (0 : ℝ)..t, (Real.cos u - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * u ^ (2 * i) / (2 * i)!)| := by
        rw [intervalIntegral.integral_sub (by simp)]
        · rw [intervalIntegral.integral_finset_sum (by simp)]
          norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Nat.factorial_succ]
        · exact Continuous.intervalIntegrable (by fun_prop) _ _
      -- Apply the induction hypothesis to the integral inside the absolute value.
      have h_ind : |∫ u in (0 : ℝ)..t, (Real.cos u - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * u ^ (2 * i) / (2 * i)!)| ≤ ∫ u in (0 : ℝ)..t, |u| ^ (2 * n) / (2 * n)! := by
        rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
        refine le_trans (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)) ( MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_)
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
        · exact Continuous.integrableOn_Ioc ( by fun_prop )
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using ih u
      convert h_ind using 1
      rw [intervalIntegral.integral_congr fun u hu => by rw [abs_of_nonneg]; linarith only [ Set.mem_Icc.mp ( by simpa [ ht.1 ] using hu )]]
      simp only [mul_comm, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
        Nat.cast_one, div_eq_mul_inv, mul_inv_rev, mul_assoc, intervalIntegral.integral_mul_const,
        integral_pow, zero_mul, sub_zero, mul_left_comm]
      rw [abs_of_nonneg ht.1]
    -- Apply the induction hypothesis to bound the integral.
    have h_integral_bound : |∫ t in (0 : ℝ)..x, (Real.sin t - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * t ^ (2 * i + 1) / (2 * i + 1)!)| ≤ ∫ t in (0 : ℝ)..|x|, |t| ^ (2 * n + 1) / (2 * n + 1)! := by
      obtain hx | hx := abs_cases x <;> simp_all [intervalIntegral]
      · rw [abs_of_nonneg hx]
        refine le_trans (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)) ?_
        refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
        · exact Continuous.integrableOn_Ioc (by fun_prop)
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using h_ind t ht.1.le ht.2;
      · refine le_trans (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)) ?_
        refine le_trans (MeasureTheory.integral_mono_of_nonneg
                         (g := fun (t:ℝ) ↦ |t| ^ (2 * n + 1) / (2 * n + 1)!) ?_ ?_ ?_) ?_
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
        · exact Continuous.integrableOn_Ioc (by fun_prop)
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht
          convert h_ind (-t) (by grind) (by grind) using 1 <;> norm_num [abs_neg, abs_of_nonpos, ht.1.le, ht.2]
          simp only [pow_succ', even_two, Even.mul_right, Even.neg_pow, neg_mul, mul_neg, neg_div,
            Finset.sum_neg_distrib, sub_neg_eq_add]
          rw [ neg_add_eq_sub, abs_sub_comm ]
        · rw [← intervalIntegral.integral_of_le hx.1, ← intervalIntegral.integral_of_le (abs_nonneg x)]
          convert intervalIntegral.integral_comp_neg _ |> le_of_eq using 2 <;> norm_num [abs_of_nonpos hx.1]
    refine h_rewrite ▸ h_integral_bound.trans ?_
    rw [intervalIntegral.integral_congr fun t ht => by rw [abs_of_nonneg]; aesop]
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one, intervalIntegral.integral_div, Nat.mul_succ]
    simp only [← pow_succ, integral_pow, ne_eq, Nat.add_eq_zero_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, one_ne_zero, and_false, and_self, not_false_eq_true, zero_pow,
      sub_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one];
    rw [div_div]

theorem cos_psum_eq_real_sum (n : ℕ) (x : ℚ) : (RationalApprox.cos_psum n x : ℝ) = ∑ i ∈ Finset.range n, (-1)^i * (x : ℝ)^(2*i) / (2*i)! := by
  simp only [cos_psum, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_div, Rat.cast_natCast]
  simp_rw [mul_div_assoc']

end AristotleLemmas

theorem sin_psum_approx (x : ℚ) (n : ℕ) : |Real.sin x - sin_psum n x| ≤ |x|^(2 * n + 1) / (2 * n + 1)! := by
  have := RationalApprox.sin_approx_aux x n
  simp_all only [Rat.cast_abs, ge_iff_le]
  convert this using 4
  norm_cast
  refine Finset.sum_congr rfl fun _ _ => ?_
  aesop

theorem cos_psum_approx (x : ℚ) (n : ℕ) : |Real.cos x - cos_psum n x| ≤ |x|^(2 * n) / (2 * n)! := by
  rw [Rat.cast_abs x, cos_psum_eq_real_sum n x]
  exact Real.cos_approx_sum (x : ℝ) n

theorem sinℚ_approx (x : ℚ) : |Real.sin x - sinℚ x| ≤ |x|^27 / 27! :=
  sin_psum_approx x 13

theorem cosℚ_approx (x : ℚ) : |Real.cos x - cosℚ x| ≤ |x|^26 / 26! :=
  cos_psum_approx x 13

theorem sinℚ_approx' (x : ℚ) (hx : x ∈ Set.Icc (-4) 4) : |Real.sin x - sinℚ x| ≤ κ / 7 := by
  have hx' : |x| ≤ 4 := abs_le.mpr hx
  have z := sinℚ_approx x
  grw [hx'] at z
  have : 4 ^ 27 / ↑27! ≤ κ / 7 := by
    norm_num [κ]
  grw [← this]
  exact z

theorem cosℚ_approx' (x : ℚ) (hx : x ∈ Set.Icc (-4) 4) : |Real.cos x - cosℚ x| ≤ κ / 7 := by
  have hx' : |x| ≤ 4 := abs_le.mpr hx
  have z := cosℚ_approx x
  grw [hx'] at z
  have : 4 ^ 26 / ↑26! ≤ κ / 7 := by
    norm_num [κ]
  grw [← this]
  exact z

inductive RewritableEntry : Type where
  | zero : RewritableEntry
  | one : RewritableEntry
  | minus_one : RewritableEntry
  | sin : RewritableEntry
  | cos : RewritableEntry
  | msin : RewritableEntry
  | mcos : RewritableEntry

def DistLtKappaEntry := RewritableEntry × RewritableEntry

noncomputable
def RewritableEntry.actual (z : ℚ) : RewritableEntry → ℝ
| .zero => 0
| .one => 1
| .minus_one => -1
| .sin => Real.sin z
| .cos => Real.cos z
| .msin => -Real.sin z
| .mcos => -Real.cos z

noncomputable
def DistLtKappaEntry.actual (dlke : DistLtKappaEntry) (x y : ℚ) :=
  dlke.fst.actual x * dlke.snd.actual y

noncomputable
def RewritableEntry.approx (z : ℚ) : RewritableEntry → ℝ
| .zero => 0
| .one => 1
| .minus_one => -1
| .sin => sinℚ z
| .cos => cosℚ z
| .msin => -sinℚ z
| .mcos => -cosℚ z

noncomputable
def DistLtKappaEntry.approx (dlke : DistLtKappaEntry) (x y : ℚ) :=
  dlke.fst.approx x * dlke.snd.approx y

noncomputable
def matrixActual {m n : ℕ} (A : Matrix (Fin m) (Fin n) DistLtKappaEntry) (x y : ℚ) : E n →L[ℝ] E m :=
   A.map (·.actual x y) |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def matrixApprox {m n : ℕ} (A : Matrix (Fin m) (Fin n) DistLtKappaEntry) (x y : ℚ) : E n →L[ℝ] E m :=
   A.map (·.approx x y) |>.toEuclideanLin.toContinuousLinearMap

theorem norm_matrix_actual_approx_le_kappa {m n : Finset.Icc 1 3} (A : Matrix (Fin m) (Fin n) DistLtKappaEntry) (x y : Set.Icc (-4) 4) :
    ‖matrixActual A x y - matrixApprox A x y‖ ≤ κ := by
  sorry
