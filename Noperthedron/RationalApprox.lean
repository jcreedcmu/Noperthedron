import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Int.Star
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

noncomputable section AristotleLemmas

/--
The sum of the first n odd terms of the sine Taylor series equals the Taylor polynomial of degree 2n.
-/
theorem sin_taylor_poly_eq (n : ℕ) (x : ℝ) :
    ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!) =
    taylorWithinEval Real.sin (2 * n) Set.univ 0 x := by
  -- By definition of taylorWithinEval, we can expand it using taylor_within_apply.
  have h_taylor :
      taylorWithinEval Real.sin (2 * n) Set.univ 0 x =
      ∑ i ∈ Finset.range (2 * n + 1), (iteratedDeriv i Real.sin 0) * x ^ i / (i ! : ℝ) := by
    rw [taylorWithinEval]
    -- By definition of taylorWithin, we can expand it using the sum of the terms
    -- up to the 2n-th derivative.
    simp [taylorWithin, taylorCoeffWithin, div_eq_inv_mul, mul_comm,
          mul_left_comm, iteratedDerivWithin_univ]
  -- Split the sum into even and odd indices. For even indices, the iterated derivative of sin at 0 is zero.
  have h_split : ∑ i ∈ Finset.range (2 * n + 1), (iteratedDeriv i Real.sin 0) * x ^ i / (i ! : ℝ) = ∑ i ∈ Finset.filter (fun i => i % 2 = 1) (Finset.range (2 * n + 1)), (iteratedDeriv i Real.sin 0) * x ^ i / (i ! : ℝ) := by
    rw [Finset.sum_filter, Finset.sum_congr rfl]
    intro x_1 a
    simp_all only [Finset.mem_range, left_eq_ite_iff, Nat.mod_two_not_eq_one, div_eq_zero_iff,
                   mul_eq_zero, pow_eq_zero_iff', ne_eq, Nat.cast_eq_zero]
    intro a_1
    rw [← Nat.mod_add_div x_1 2 ]
    norm_num [a_1, iteratedDeriv_succ, Real.sin_zero, Real.cos_zero]
  -- The sum of the odd terms in the Taylor series of sin(x) up to 2n is exactly the sum of the terms where the exponent is 2i+1.
  have h_odd_terms : Finset.filter (fun i => i % 2 = 1) (Finset.range (2 * n + 1)) =
                     Finset.image (fun i => 2 * i + 1) (Finset.range n) := by
    ext i
    cases i with
    | zero => simp
    | succ i =>
      simp only [Finset.mem_filter, Finset.mem_range, add_lt_add_iff_right, Finset.mem_image,
        Nat.add_right_cancel_iff]
      exact ⟨ fun hi => ⟨ i / 2, by cutsat, by cutsat⟩, fun hi => by cutsat ⟩
  field_simp
  aesop

set_option maxHeartbeats 300000 in
/--
The error of the degree $2n$ Taylor polynomial for sine is bounded by $|x|^{2n+1}/(2n+1)!$.
-/
theorem sin_approx_aux (x : ℝ) (n : ℕ) :
    |Real.sin x - ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)| ≤
    |x| ^ (2 * n + 1) / (2 * n + 1)! := by
  suffices H :
      |Real.sin x - ∑ x_1 ∈ Finset.range n, (-1) ^ x_1 * x ^ (2 * x_1 + 1) /
       ↑(2 * x_1 + 1)!| * ↑(2 * n + 1)! ≤
      |x| ^ (2 * n + 1) by
    field_simp
    exact H
  -- Apply the taylorMeanRemainderLagrange theorem to the interval [0, x].
  have h_taylor_mean : ∀ x : ℝ, 0 ≤ x → |Real.sin x - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)| ≤ |x| ^ (2 * n + 1) / (2 * n + 1)! := by
    -- Apply the Lagrange form of the remainder for the Taylor series of sin(x).
    have h_lagrange : ∀ x : ℝ, 0 ≤ x → ∃ c ∈ Set.Icc 0 x, Real.sin x - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!) = (iteratedDeriv (2 * n + 1) Real.sin c) * x ^ (2 * n + 1) / (2 * n + 1)! := by
      intro x hx
      have := @taylor_mean_remainder_lagrange
      by_cases hx' : x = 0
      · aesop
      · -- Apply the Lagrange remainder theorem with the given parameters.
        have := @this (fun x => Real.sin x) x 0 (2 * n) (by positivity) Real.contDiff_sin.contDiffOn
                (by
        refine' DifferentiableOn.congr _ _;
        · use fun x => Real.sin ( x + Real.pi * n )
        · exact Differentiable.differentiableOn ( Real.differentiable_sin.comp ( differentiable_id.add_const _ ) );
        · intro y hy; rw [ iteratedDerivWithin_eq_iterate ];
          -- By induction on $n$, we can show that the $2n$-th derivative of $\sin(x)$ is $\sin(x + n\pi)$.
          have h_ind : ∀ n : ℕ, deriv^[2 * n] Real.sin = fun x => Real.sin (x + n * Real.pi) := by
            intro n
            induction n <;> simp_all +decide [Nat.mul_succ, Function.iterate_succ_apply', Real.sin_add]
            norm_num [add_mul, Real.sin_add, Real.cos_add]
          convert congr_fun ( h_ind n ) y using 1
          · induction' 2 * n with n ih generalizing y <;> simp_all +decide [ Function.iterate_succ_apply' ]
            -- Since $y \in (0, x)$, the derivative within the interval $[0, x]$ at $y$ is the same as the regular derivative.
            have h_deriv_eq : derivWithin ((fun g => derivWithin g (Set.Icc 0 x))^[n] (fun x => Real.sin x)) (Set.Icc 0 x) y = deriv ((fun g => derivWithin g (Set.Icc 0 x))^[n] (fun x => Real.sin x)) y := by
              rw [ derivWithin_of_mem_nhds ( Icc_mem_nhds hy.1 hy.2 ) ];
            rw [ h_deriv_eq, Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hy.1 hy.2 ) fun z hz => ih z hz.1 hz.2 ) ];
          · ring_nf);
        obtain ⟨ c, hc₁, hc₂ ⟩ := this;
        -- Since the iterated derivative within the interval [0, x] is the same as the regular derivative, we can replace the iterated derivative within the interval with the regular derivative.
        have h_iterated_deriv : iteratedDerivWithin (2 * n + 1) Real.sin (Set.Icc 0 x) c = iteratedDeriv (2 * n + 1) Real.sin c := by
          rw [ iteratedDerivWithin_eq_iteratedDeriv ];
          · exact uniqueDiffOn_Icc ( by linarith [ hc₁.1, hc₁.2 ] );
          · exact Real.contDiff_sin.contDiffAt;
          · exact Set.Ioo_subset_Icc_self hc₁;
        simp_all +decide [ taylorWithinEval ];
        -- By definition of the polynomial, we can rewrite the left-hand side of the equation.
        have h_poly_eval : PolynomialModule.eval x (taylorWithin (fun x => Real.sin x) (2 * n) (Set.Icc 0 x) 0) = ∑ i ∈ Finset.range (2 * n + 1), (iteratedDeriv i Real.sin 0) * x ^ i / (i ! : ℝ) := by
          unfold taylorWithin
          simp_all only [map_zero, sub_zero, PolynomialModule.comp_apply, PolynomialModule.map_single,
            PolynomialModule.eval_single, map_sum, PolynomialModule.eval_smul, Polynomial.eval_pow, Polynomial.eval_X,
            PolynomialModule.eval_lsingle, pow_zero, smul_eq_mul, one_mul]
          obtain ⟨left, right⟩ := hc₁
          unfold taylorCoeffWithin
          simp_all only [smul_eq_mul]
          refine' Finset.sum_congr rfl fun i hi => _
          rw [iteratedDerivWithin_eq_iteratedDeriv]
          · ring_nf
          · exact uniqueDiffOn_Icc (by linarith)
          · exact Real.contDiff_sin.contDiffAt
          · constructor <;> linarith
        -- Since the iterated derivative of sin at 0 is zero for even i, we can split the sum into even and odd terms.
        have h_split_sum :
            ∑ i ∈ Finset.range (2 * n + 1),
              (iteratedDeriv i Real.sin 0) * x ^ i / (i ! : ℝ) =
            ∑ i ∈ Finset.range n, (iteratedDeriv (2 * i + 1) Real.sin 0) * x ^ (2 * i + 1) /
               ((2 * i + 1)! : ℝ) := by
          have h_split_sum : Finset.range (2 * n + 1) =
              Finset.image (fun i => 2 * i) (Finset.range (n + 1)) ∪
              Finset.image (fun i => 2 * i + 1) (Finset.range n) := by
            ext i
            simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
            refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
            · rcases Nat.even_or_odd' i with ⟨ k, rfl | rfl ⟩ <;> [left; right] <;>
                exact ⟨ k, by linarith, rfl ⟩
            · rcases hi with ( ⟨ k, hk, rfl ⟩ | ⟨ k, hk, rfl ⟩ ) <;> linarith
          rw [h_split_sum, Finset.sum_union]
          · norm_num
          · simp only [Finset.disjoint_right, Finset.mem_image, Finset.mem_range, forall_exists_index]
            cutsat
        have h_iterated_deriv : ∀ i : ℕ, iteratedDeriv (2 * i + 1) Real.sin 0 = (-1 : ℝ) ^ i := by
          simp
        use c
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        clear this
        simp_all +decide [mul_div_assoc]
    intro x hx
    specialize h_lagrange x hx
    simp_all only [Set.mem_Icc, Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_even_cos,
      Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply]
    obtain ⟨w, h⟩ := h_lagrange
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_1⟩ := left
    simp_all only
    simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, fieldLe]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)
  by_cases hx : 0 ≤ x
  · simpa only [mul_div_assoc] using
     le_trans (mul_le_mul_of_nonneg_right (h_taylor_mean x hx) (by positivity))
              (by rw [div_mul_cancel₀ _ (by positivity)])
  · have := h_taylor_mean (-x) (by linarith)
    simp_all only [not_le, Real.sin_neg, abs_neg, ge_iff_le]
    convert mul_le_mul_of_nonneg_right this ( Nat.cast_nonneg ( 2 * n + 1 ) ! ) using 1
    · simp only [mul_comm, pow_add, pow_one, mul_assoc, div_eq_mul_inv, mul_left_comm, even_two,
        Even.mul_left, Even.neg_pow, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add,
        mul_eq_mul_left_iff, Nat.cast_eq_zero]
      left
      rw [← abs_neg]
      ring_nf
    · rw [div_mul_cancel₀ _ (by positivity)]

end AristotleLemmas

theorem sin_psum_approx (x : ℚ) (n : ℕ) : |Real.sin x - sin_psum n x| ≤ |x|^(2 * n + 1) / (2 * n + 1)! := by
  have := RationalApprox.sin_approx_aux x n
  simp_all only [Rat.cast_abs, ge_iff_le]
  convert this using 4
  norm_cast
  refine Finset.sum_congr rfl fun _ _ => ?_
  aesop

theorem cos_psum_approx (x : ℚ) (n : ℕ) : |Real.cos x - cos_psum n x| ≤ |x|^(2 * n) / (2 * n)! := by
  sorry

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
