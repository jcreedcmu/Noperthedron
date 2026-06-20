import Noperthedron.Basic
import Noperthedron.RationalApprox.TrigLemmas
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Vertex approximation bounds

Proves that the approximate Rz rotation (using sinℚ/cosℚ) is within κ
of the real Rz rotation, for angles in [-4, 4] and unit-norm vectors.

## Key result

`rz_approx_error`: ‖RzL(θ)(v) - rzApprox(θ)(v)‖ ≤ κ

The proof decomposes the error into coordinates, uses sinℚ_approx'/cosℚ_approx'
to bound each trig difference by κ/7, and shows the total norm error is
≤ √2·κ/7 < κ.
-/

namespace Solution

open Real RationalApprox

/-! ### Angle range lemmas -/

/-- The reduced rotation index is always ≤ 7. -/
lemma reduceK_le_seven (k : ℕ) : (if k % 15 ≤ 7 then k % 15 else 15 - k % 15) ≤ 7 := by
  split
  · assumption
  · omega

/-- The rotation angle `2πk/15` lies in `[-4, 4]` for `k ≤ 7`. -/
lemma angle_in_range (k : ℕ) (hk : k ≤ 7) :
    2 * π * (k : ℝ) / 15 ∈ Set.Icc (-4 : ℝ) 4 := by
  refine ⟨?_, ?_⟩
  · have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have : 0 < π := pi_pos
    nlinarith
  · have hk' : (k : ℝ) ≤ 7 := by exact_mod_cast hk
    have hpi : π < 4 := pi_lt_four
    nlinarith

/-- The reduced rotation angle lies in `[-4, 4]`. -/
lemma reduced_angle_in_range (k : ℕ) :
    2 * π * (↑(if k % 15 ≤ 7 then k % 15 else 15 - k % 15) : ℝ) / 15 ∈
      Set.Icc (-4 : ℝ) 4 :=
  angle_in_range _ (reduceK_le_seven k)

/-! ### Approximate Rz rotation -/

/-- Approximate Rz rotation using sinℚ/cosℚ. -/
noncomputable def rzApprox (θ : ℝ) (v : ℝ³) : ℝ³ :=
  WithLp.toLp 2 fun
    | 0 => cosℚ θ * v 0 - sinℚ θ * v 1
    | 1 => sinℚ θ * v 0 + cosℚ θ * v 1
    | 2 => v 2

/-! ### Main error bound -/

/-- The approximate Rz rotation is within κ of the real rotation,
    for angles in [-4, 4] and vectors with ‖v‖ ≤ 1.

    Proof: the error decomposes as
    `‖d‖² = (Δc² + Δs²)(v₀² + v₁²) ≤ 2(κ/7)² · 1`
    so `‖d‖ ≤ √2 · κ/7 < κ`. -/
lemma rz_approx_error (θ : ℝ) (v : ℝ³) (hθ : θ ∈ Set.Icc (-4 : ℝ) 4) (hv : ‖v‖ ≤ 1) :
    ‖RzL θ v - rzApprox θ v‖ ≤ κ := by
  set d := RzL θ v - rzApprox θ v
  set Δc := cos θ - cosℚ θ
  set Δs := sin θ - sinℚ θ
  have hd0 : d 0 = Δc * v 0 - Δs * v 1 := by
    simp [d, RzL, Rz_mat, rzApprox, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail, Δc, Δs]; ring
  have hd1 : d 1 = Δs * v 0 + Δc * v 1 := by
    simp [d, RzL, Rz_mat, rzApprox, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail, Δc, Δs]; ring
  have hd2 : d 2 = 0 := by
    simp [d, RzL, Rz_mat, rzApprox, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]
  have hnorm_sq : ‖d‖ ^ 2 = (Δc ^ 2 + Δs ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs, hd0, hd1, hd2]; ring
  have hΔc : |Δc| ≤ κ / 7 := cosℚ_approx' θ hθ
  have hΔs : |Δs| ≤ κ / 7 := sinℚ_approx' θ hθ
  have h1 : Δc ^ 2 ≤ (κ / 7) ^ 2 := by
    nlinarith [neg_abs_le Δc, le_abs_self Δc, sq_nonneg (κ/7 - Δc), sq_nonneg (κ/7 + Δc)]
  have h2 : Δs ^ 2 ≤ (κ / 7) ^ 2 := by
    nlinarith [neg_abs_le Δs, le_abs_self Δs, sq_nonneg (κ/7 - Δs), sq_nonneg (κ/7 + Δs)]
  have hv_sq : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := by
    have hvn : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]; simp [Real.norm_eq_abs, sq_abs]
    have hvsq : ‖v‖ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (‖v‖ - 1), sq_nonneg (‖v‖ + 1), norm_nonneg v]
    nlinarith [sq_nonneg (v 2)]
  have hnorm_bound : ‖d‖ ^ 2 ≤ 2 * (κ / 7) ^ 2 := by
    rw [hnorm_sq]; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hκ : (0 : ℝ) < κ := by norm_num [κ]
  suffices h : ‖d‖ ≤ √2 * κ / 7 by
    linarith [show √2 * κ / 7 < κ from by
      nlinarith [show √2 < 2 from by
        calc √2 < √(2^2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          _ = 2 := by rw [Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]]]
  rw [← Real.sqrt_sq (norm_nonneg d)]
  calc √(‖d‖ ^ 2)
      ≤ √(2 * (κ / 7) ^ 2) := Real.sqrt_le_sqrt hnorm_bound
    _ = √2 * (κ / 7) := by
        rw [Real.sqrt_mul (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_sq (by positivity)]
    _ = √2 * κ / 7 := by ring

end Solution
