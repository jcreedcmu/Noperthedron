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
import Noperthedron.Lemma42
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

theorem finset_sum_range_even_odd' {n : ℕ} {f : ℕ → ℝ}
    : ∑ i ∈ Finset.range (2 * n), f i =
      ∑ i ∈ Finset.range n, f (2 * i + 1) + ∑ i ∈ Finset.range n, f (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
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
  obtain ⟨c, -, hc₂⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 2 * n) hx Real.contDiff_sin.contDiffOn
  simp only [taylorWithinEval_sin hx, sub_zero] at hc₂
  simp only [hc₂, Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_even_cos, Pi.mul_apply,
    Pi.pow_apply, Pi.neg_apply, Pi.ofNat_apply]
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, fieldLe]
  exact Real.abs_cos_le_one c

theorem taylorWithinEval_cos {n : ℕ} {x : ℝ} (hx' : 0 < x) :
    taylorWithinEval Real.cos (2 * n + 1) (Set.Icc 0 x) 0 x =
       ∑ i ∈ Finset.range (n + 1), (-1) ^ i * x ^ (2 * i) / ↑(2 * i)! := by
  have h_poly_eval : taylorWithinEval Real.cos (2 * n + 1) (Set.Icc 0 x) 0 x =
       ∑ i ∈ Finset.range (2 * n + 1 + 1), (iteratedDeriv i Real.cos 0) * x ^ i / (i ! : ℝ) := by
    rw [taylor_within_apply]
    congr; ext i
    rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc hx') Real.contDiff_cos.contDiffAt (Set.left_mem_Icc.mpr hx'.le)]
    simp [field]
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring] at h_poly_eval
  rw [finset_sum_range_even_odd'] at h_poly_eval
  rw [h_poly_eval]
  simp [mul_div_assoc]

/--
The difference between cos(x) and its Taylor polynomial of degree 2n-2 is bounded by |x|^(2n)/(2n)!.
-/
theorem cos_approx_aux (x : ℝ) (n : ℕ) :
    |Real.cos x - ∑ i ∈ Finset.range n, (-1)^i * x^(2*i) / (2*i)!| ≤ |x|^(2*n) / (2*n)! := by
  cases n with
  | zero => simpa using Real.abs_cos_le_one x
  | succ n =>
    rw [le_div_iff₀ (by positivity)]
    wlog hx : 0 < x with H
    · obtain rfl | hx := eq_or_lt_of_not_gt hx
      · simp [Finset.sum_range_succ']
      · specialize H (-x) n (by linarith)
        simpa using H
    obtain ⟨c, hc₁, hc₂⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 2 * n + 1) hx Real.contDiff_cos.contDiffOn
    simp only [taylorWithinEval_cos hx, sub_zero] at hc₂
    simp only [hc₂, show 2 * n + 1 + 1 = 2 * (n + 1) by linarith]
    simp only [Real.iteratedDeriv_even_cos, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply,
      abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, fieldLe]
    exact Real.abs_cos_le_one c

theorem sin_psum_approx (x : ℚ) (n : ℕ) : |Real.sin x - sin_psum n x| ≤ |x|^(2 * n + 1) / (2 * n + 1)! := by
  have := RationalApprox.sin_approx_aux x n
  simp only [Rat.cast_abs, ge_iff_le]
  convert this using 3
  norm_cast
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp

theorem cos_psum_approx (x : ℚ) (n : ℕ) : |Real.cos x - cos_psum n x| ≤ |x|^(2 * n) / (2 * n)! := by
  have := RationalApprox.cos_approx_aux x n
  simp only [Rat.cast_abs, ge_iff_le]
  convert this using 3
  norm_cast
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp [field]

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

section AristotleLemmas

/--
The actual value of any `RewritableEntry` (which can be 0, 1, -1, sin(z), cos(z), -sin(z), -cos(z))
is bounded by 1 in absolute value.
-/
theorem rewritable_entry_bound (e : RationalApprox.RewritableEntry) (z : ℚ) :
    |e.actual z| ≤ 1 := by
  cases e <;> simp [RewritableEntry.actual, Real.abs_sin_le_one, Real.abs_cos_le_one]

/--
The error between the actual value and the rational approximation for any `RewritableEntry` is at
most `κ / 7` for inputs in `[-4, 4]`.
-/
theorem rewritable_entry_error (e : RationalApprox.RewritableEntry) (z : ℚ)
    (hz : z ∈ Set.Icc (-4 : ℚ) 4) : |e.actual z - e.approx z| ≤ κ / 7 := by
  rcases e with ( _ | _ | _ | _ | _ | _ | _ )
  all_goals
    simp [RewritableEntry.actual, RewritableEntry.approx]
  any_goals exact div_nonneg (by unfold RationalApprox.κ; norm_num) (by norm_num)
  · exact sinℚ_approx' z hz
  · exact cosℚ_approx' z hz
  · refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [abs_le.mp (sinℚ_approx' z hz)]
    · linarith [abs_le.mp (sinℚ_approx' z hz)]
  · convert cosℚ_approx' z hz using 1
    ring_nf
    rw [neg_add_eq_sub, abs_sub_comm]

/-
The error of the product of two `RewritableEntry` approximations is bounded by `2 * κ / 7 + κ^2 / 49`.
-/
theorem dist_lt_kappa_entry_error (d : RationalApprox.DistLtKappaEntry) (x y : ℚ)
    (hx : x ∈ Set.Icc (-4 : ℚ) 4) (hy : y ∈ Set.Icc (-4 : ℚ) 4) :
    |d.actual x y - d.approx x y| ≤ 2 * κ / 7 + κ^2 / 49 := by
  -- Using the triangle inequality for the absolute value and the bounds from
  -- `rewritable_entry_bound` and `rewritable_entry_error`, we get:
  have h_abs (e1 e2 : RationalApprox.RewritableEntry) (x y : ℚ)
        (hx : x ∈ Set.Icc (-4 : ℚ) 4) (hy : y ∈ Set.Icc (-4 : ℚ) 4) :
        |e1.actual x * e2.actual y - e1.approx x * e2.approx y| ≤
        |e1.actual x| * |e2.actual y - e2.approx y| +
        |e1.actual x - e1.approx x| * |e2.approx y| := by
      rw [← abs_mul, ← abs_mul, mul_sub, sub_mul]
      exact abs_sub_le _ _ _
  -- Applying the bounds from `rewritable_entry_bound` and `rewritable_entry_error`, we get:
  have h_bound (e1 e2 : RationalApprox.RewritableEntry) (x y : ℚ)
        (hx : x ∈ Set.Icc (-4 : ℚ) 4) (hy : y ∈ Set.Icc (-4 : ℚ) 4) :
        |e1.actual x| ≤ 1 ∧ |e2.actual y| ≤ 1 ∧ |e1.approx x| ≤ 1 + κ / 7 ∧
        |e2.approx y| ≤ 1 + RationalApprox.κ / 7 := by
      have h_bound_e1 : |e1.actual x| ≤ 1 := rewritable_entry_bound e1 x
      have h_bound_e2 : |e2.actual y| ≤ 1 := rewritable_entry_bound e2 y
      have h_bound_e1_approx : |e1.approx x| ≤ 1 + RationalApprox.κ / 7 := by
        have := rewritable_entry_error e1 x hx
        rw [abs_le] at *
        constructor <;> linarith
      have h_bound_e2_approx : |e2.approx y| ≤ 1 + RationalApprox.κ / 7 := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · linarith [ abs_le.mp h_bound_e2, abs_le.mp ( rewritable_entry_error e2 y hy ) ]
        · linarith [ abs_le.mp h_bound_e2, abs_le.mp ( rewritable_entry_error e2 y hy ) ]
      exact ⟨h_bound_e1, h_bound_e2, h_bound_e1_approx, h_bound_e2_approx⟩
  -- Applying the bounds from `rewritable_entry_error`, we get:
  have h_error (e1 e2 : RewritableEntry) (x y : ℚ)
      (hx : x ∈ Set.Icc (-4 : ℚ) 4) (hy : y ∈ Set.Icc (-4 : ℚ) 4) :
      |e1.actual x - e1.approx x| ≤ RationalApprox.κ / 7 ∧
      |e2.actual y - e2.approx y| ≤ RationalApprox.κ / 7 := by
    exact ⟨rewritable_entry_error e1 x hx, rewritable_entry_error e2 y hy⟩
  have := h_abs d.1 d.2 x y hx hy
  have := h_bound d.1 d.2 x y hx hy
  have := h_error d.1 d.2 x y hx hy
  simp only [Set.mem_Icc, and_imp] at *
  refine le_trans ‹_› ?_
  nlinarith [
    abs_nonneg (RewritableEntry.actual x d.1),
    abs_nonneg (RewritableEntry.actual y d.2 - RewritableEntry.approx y d.2),
    abs_nonneg (RewritableEntry.actual x d.1 - RewritableEntry.approx x d.1),
    abs_nonneg (RewritableEntry.approx y d.2 ),
    show 0 ≤ κ by exact div_nonneg zero_le_one <| by norm_num]

/--
The error bound `3 * (2 * κ / 7 + κ^2 / 49)` is less than or equal to `κ`.
-/
theorem kappa_bound_aux : 3 * (2 * κ / 7 + κ^2 / 49) ≤ κ := by norm_num [κ]

end AristotleLemmas

theorem norm_matrix_actual_approx_le_kappa {m n : Finset.Icc 1 3}
    (A : Matrix (Fin m) (Fin n) DistLtKappaEntry) (x y : Set.Icc (-4) 4) :
    ‖matrixActual A x y - matrixApprox A x y‖ ≤ κ := by
  -- Let's choose δ as the upper bound from `dist_lt_kappa_entry_error`.
  set δ := 2 * κ / 7 + κ^2 / 49 with hδ_def
  have hδ_pos : 0 < δ := by
    norm_num [ hδ_def, RationalApprox.κ ]
  have hδ_bound : ∀ i j, |(A.map (fun d => d.actual (x.val) (y.val)) i j) -
                          (A.map (fun d => d.approx (x.val) (y.val)) i j)| ≤ δ := by
    intro i j
    apply RationalApprox.dist_lt_kappa_entry_error
    · exact ⟨mod_cast x.2.1, mod_cast x.2.2⟩
    · decide +revert
  have h_sqrt_bound : Real.sqrt (m.val * n.val) ≤ 3 := by
    refine Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
    · positivity
    · norm_cast
      nlinarith [ Finset.mem_Icc.mp m.2, Finset.mem_Icc.mp n.2 ]
  -- Applying the norm bound from `norm_le_delta_sqrt_dims`.
  have norm_le_delta_sqrt_dims_applied :
      ‖(A.map (fun d => d.actual (x.val) (y.val)) -
        A.map (fun d => d.approx (x.val) (y.val))).toEuclideanLin.toContinuousLinearMap‖ ≤
      δ * Real.sqrt (m.val * n.val) := by
    convert norm_le_delta_sqrt_dims _ hδ_pos hδ_bound using 1
  refine le_trans ?_ ( norm_le_delta_sqrt_dims_applied.trans ?_)
  · simp_all [matrixActual, matrixApprox]
  · refine le_trans ( mul_le_mul_of_nonneg_left h_sqrt_bound <| by positivity ) ?_
    linarith [kappa_bound_aux]
