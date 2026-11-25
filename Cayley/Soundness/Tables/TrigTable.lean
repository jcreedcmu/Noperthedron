module

public import Cayley.Soundness.Tables.Trig
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# The checker's trigonometric tables

`cos(2πk/15)` and `sin(2πk/15)` are within `2⁻⁷¹` of `cosTab` and `sinTab`: the case
`k = 1` comes from `Cayley.Soundness.Tables.Trig`, and the multiples follow by complex
multiplication with the error tracked step by step.
-/

namespace Cayley

open Real

/-- The table entries, as integers over `2^80`. -/
def cosM (k : ℕ) : ℤ := cosTab.getD k 0
def sinM (k : ℕ) : ℤ := sinTab.getD k 0

/-- The exact point `e^(ikθ₁)`. -/
noncomputable def zc (k : ℕ) : ℂ := ⟨cos (k * θ₁), sin (k * θ₁)⟩

/-- The table point. -/
noncomputable def zt (k : ℕ) : ℂ := ⟨(cosM k : ℝ) / 2 ^ 80, (sinM k : ℝ) / 2 ^ 80⟩

theorem zc_succ (k : ℕ) : zc (k + 1) = zc k * zc 1 := by
  apply Complex.ext <;> simp [zc, Complex.mul_re, Complex.mul_im, add_mul, cos_add, sin_add]
  ring

theorem norm_zc (k : ℕ) : ‖zc k‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp [zc, cos_sq_add_sin_sq]

theorem norm_le_re_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z

theorem zc_one_err : ‖zc 1 - zt 1‖ ≤ 1 / 2 ^ 79 := by
  refine le_trans (norm_le_re_im _) ?_
  have hc := cos_θ₁_bounds
  have hs := sin_θ₁_bounds
  simp only [zc, zt, Complex.sub_re, Complex.sub_im, Nat.cast_one, one_mul]
  have h1 : |cos θ₁ - (cosM 1 : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 80 := by
    rw [abs_le, show cosM 1 = 1104408691135802787572491 from rfl]
    constructor <;> norm_num <;> linarith [hc.1, hc.2]
  have h2 : |sin θ₁ - (sinM 1 : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 80 := by
    rw [abs_le, show sinM 1 = 491714429597714652495797 from rfl]
    constructor <;> norm_num <;> linarith [hs.1, hs.2]
  calc _ ≤ 1 / 2 ^ 80 + 1 / 2 ^ 80 := add_le_add h1 h2
    _ = 1 / 2 ^ 79 := by norm_num

/-- The computable step error of the recurrence. -/
theorem step_err (k : ℕ) (E : ℝ) (hk : ‖zc k - zt k‖ ≤ E) :
    ‖zc (k + 1) - zt (k + 1)‖ ≤ E + (|(zt k).re| + |(zt k).im|) * (1 / 2 ^ 79) +
      (|(zt k * zt 1 - zt (k + 1)).re| + |(zt k * zt 1 - zt (k + 1)).im|) := by
  have e1 := zc_one_err
  rw [zc_succ]
  calc ‖zc k * zc 1 - zt (k + 1)‖
      = ‖(zc k - zt k) * zc 1 + zt k * (zc 1 - zt 1) + (zt k * zt 1 - zt (k + 1))‖ := by
        congr 1; ring
    _ ≤ ‖(zc k - zt k) * zc 1‖ + ‖zt k * (zc 1 - zt 1)‖ + ‖zt k * zt 1 - zt (k + 1)‖ :=
        norm_add₃_le
    _ ≤ E * 1 + (|(zt k).re| + |(zt k).im|) * (1 / 2 ^ 79) +
        (|(zt k * zt 1 - zt (k + 1)).re| + |(zt k * zt 1 - zt (k + 1)).im|) := by
        rw [norm_mul, norm_mul, norm_zc]
        gcongr
        · exact norm_le_re_im _
        · exact norm_le_re_im _
    _ = _ := by ring

/-- The numerical side condition of each step, over the integers. -/
theorem step_small_int : ∀ k < 14,
    (|cosM k| + |sinM k|) * 2 +
      (|cosM k * cosM 1 - sinM k * sinM 1 - cosM (k + 1) * 2 ^ 80| +
        |cosM k * sinM 1 + sinM k * cosM 1 - sinM (k + 1) * 2 ^ 80|) ≤ 2 ^ 85 := by
  decide +kernel

theorem step_small (k : ℕ) (hk : k < 14) :
    (|(zt k).re| + |(zt k).im|) * (1 / 2 ^ 79) +
      (|(zt k * zt 1 - zt (k + 1)).re| + |(zt k * zt 1 - zt (k + 1)).im|) ≤ 1 / 2 ^ 75 := by
  have h : (((|cosM k| + |sinM k|) * 2 +
      (|cosM k * cosM 1 - sinM k * sinM 1 - cosM (k + 1) * 2 ^ 80| +
        |cosM k * sinM 1 + sinM k * cosM 1 - sinM (k + 1) * 2 ^ 80|) : ℤ) : ℝ) ≤
      ((2 ^ 85 : ℤ) : ℝ) := Int.cast_le.2 (step_small_int k hk)
  push_cast at h
  have e1 : (zt k * zt 1 - zt (k + 1)).re =
      ((cosM k : ℝ) * cosM 1 - sinM k * sinM 1 - cosM (k + 1) * 2 ^ 80) / 2 ^ 160 := by
    simp only [zt, Complex.mul_re, Complex.sub_re]; ring
  have e2 : (zt k * zt 1 - zt (k + 1)).im =
      ((cosM k : ℝ) * sinM 1 + sinM k * cosM 1 - sinM (k + 1) * 2 ^ 80) / 2 ^ 160 := by
    simp only [zt, Complex.mul_im, Complex.sub_im]; ring
  rw [e1, e2]
  simp only [zt, abs_div, abs_of_pos (show (0 : ℝ) < 2 ^ 80 by positivity),
    abs_of_pos (show (0 : ℝ) < 2 ^ 160 by positivity)]
  rw [show ∀ a b x y : ℝ, (a / 2 ^ 80 + b / 2 ^ 80) * (1 / 2 ^ 79) + (x / 2 ^ 160 + y / 2 ^ 160) =
      ((a + b) * 2 + (x + y)) / 2 ^ 160 from fun a b x y => by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num at h ⊢
  linarith

theorem trig_err (k : ℕ) (hk : k < 15) : ‖zc k - zt k‖ ≤ k / 2 ^ 75 := by
  induction k with
  | zero =>
    have : zc 0 - zt 0 = 0 := by
      apply Complex.ext <;>
        simp [zc, zt, show cosM 0 = 2 ^ 80 from rfl, show sinM 0 = 0 from rfl]
      norm_num
    simp [this]
  | succ k ih =>
    have := step_err k _ (ih (by omega))
    have := step_small k (by omega)
    push_cast
    linarith

theorem cos_tab_err (k : ℕ) (hk : k < 15) :
    |cos (2 * π * k / 15) - (cosM k : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 71 := by
  rw [show 2 * π * k / 15 = k * θ₁ by unfold θ₁; ring]
  have h := le_trans (Complex.abs_re_le_norm _) (trig_err k hk)
  simp only [zc, zt, Complex.sub_re] at h
  refine le_trans h ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (k : ℝ) ≤ 14 := by exact_mod_cast (by omega : k ≤ 14)
  nlinarith

theorem sin_tab_err (k : ℕ) (hk : k < 15) :
    |sin (2 * π * k / 15) - (sinM k : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 71 := by
  rw [show 2 * π * k / 15 = k * θ₁ by unfold θ₁; ring]
  have h := le_trans (Complex.abs_im_le_norm _) (trig_err k hk)
  simp only [zc, zt, Complex.sub_im] at h
  refine le_trans h ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (k : ℝ) ≤ 14 := by exact_mod_cast (by omega : k ≤ 14)
  nlinarith

end Cayley

end
