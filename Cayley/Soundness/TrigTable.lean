module

public import Cayley.Soundness.Trig
public import Cayley.Soundness.QIReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# The checker's trigonometric tables

`cos(2πk/15)` and `sin(2πk/15)` are within `2⁻⁷¹` of `cosTab` and `sinTab`: the case
`k = 1` comes from `Cayley.Soundness.Trig`, and the multiples follow by complex
multiplication with the error tracked step by step.
-/

namespace Cayley

open Real

def cosM : ℕ → ℤ
  | 0 => 1208925819614629174706176
  | 1 => 1104408691135802787572491
  | 2 => 808929266721616466411793
  | 3 => 373578623199582567987662
  | 4 => -126367158128905632231740
  | 5 => -604462909807314587353088
  | 6 => -978041533006897155340750
  | 7 => -1182507889921199034399455
  | 8 => -1182507889921199034399455
  | 9 => -978041533006897155340750
  | 10 => -604462909807314587353088
  | 11 => -126367158128905632231740
  | 12 => 373578623199582567987662
  | 13 => 808929266721616466411793
  | 14 => 1104408691135802787572491
  | _ => 0

def sinM : ℕ → ℤ
  | 0 => 0
  | 1 => 491714429597714652495797
  | 2 => 898406967232629382321357
  | 3 => 1149756778461952459611063
  | 4 => 1202303197482784322232552
  | 5 => 1046960471077192669696698
  | 6 => 710588767885069669736755
  | 7 => 251349811229323077289706
  | 8 => -251349811229323077289706
  | 9 => -710588767885069669736755
  | 10 => -1046960471077192669696698
  | 11 => -1202303197482784322232552
  | 12 => -1149756778461952459611063
  | 13 => -898406967232629382321357
  | 14 => -491714429597714652495797
  | _ => 0

theorem cosTab_eq (k : ℕ) (hk : k < 15) : cosTab[k]! = d80 (cosM k) := by
  interval_cases k <;> rfl

theorem sinTab_eq (k : ℕ) (hk : k < 15) : sinTab[k]! = d80 (sinM k) := by
  interval_cases k <;> rfl

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
    rw [abs_le]; simp only [cosM]; constructor <;> norm_num <;> linarith [hc.1, hc.2]
  have h2 : |sin θ₁ - (sinM 1 : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 80 := by
    rw [abs_le]; simp only [sinM]; constructor <;> norm_num <;> linarith [hs.1, hs.2]
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

/-- The numerical side condition of each step. -/
theorem step_small (k : ℕ) (hk : k < 14) :
    (|(zt k).re| + |(zt k).im|) * (1 / 2 ^ 79) +
      (|(zt k * zt 1 - zt (k + 1)).re| + |(zt k * zt 1 - zt (k + 1)).im|) ≤ 1 / 2 ^ 75 := by
  interval_cases k <;>
    simp only [zt, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, cosM, sinM] <;>
    norm_num [abs_of_nonneg, abs_of_nonpos]

theorem trig_err (k : ℕ) (hk : k < 15) : ‖zc k - zt k‖ ≤ k / 2 ^ 75 := by
  induction k with
  | zero =>
    have : zc 0 - zt 0 = 0 := by apply Complex.ext <;> simp [zc, zt, cosM, sinM] <;> norm_num
    simp [this]
  | succ k ih =>
    have := step_err k _ (ih (by omega))
    have := step_small k (by omega)
    push_cast
    linarith

theorem cos_tab_err (k : ℕ) (hk : k < 15) :
    |cos (2 * π * k / 15) - D (cosTab[k]!)| ≤ 1 / 2 ^ 71 := by
  rw [cosTab_eq k hk, D_d80, show 2 * π * k / 15 = k * θ₁ by unfold θ₁; ring]
  have h := le_trans (Complex.abs_re_le_norm _) (trig_err k hk)
  simp only [zc, zt, Complex.sub_re] at h
  refine le_trans h ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (k : ℝ) ≤ 14 := by exact_mod_cast (by omega : k ≤ 14)
  nlinarith

theorem sin_tab_err (k : ℕ) (hk : k < 15) :
    |sin (2 * π * k / 15) - D (sinTab[k]!)| ≤ 1 / 2 ^ 71 := by
  rw [sinTab_eq k hk, D_d80, show 2 * π * k / 15 = k * θ₁ by unfold θ₁; ring]
  have h := le_trans (Complex.abs_im_le_norm _) (trig_err k hk)
  simp only [zc, zt, Complex.sub_im] at h
  refine le_trans h ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (k : ℝ) ≤ 14 := by exact_mod_cast (by omega : k ≤ 14)
  nlinarith

end Cayley

end
