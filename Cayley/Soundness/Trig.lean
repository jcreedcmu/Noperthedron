module

public import Cayley.Checker.Geometry
public import Cayley.Soundness.QIReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The trigonometric constants

`cos(2πk/15)` and `sin(2πk/15)` are within `2⁻⁷⁰` of the checker's tables. For `k = 1` this
follows from the closed form `2π/15 = π/3 − π/5` with `cos(π/5) = (1 + √5)/4`; the other
multiples follow by complex multiplication, tracking the error exactly in `ℚ`.
-/

namespace Cayley

open Real

theorem sqrt5_bounds : (2.2360679774997896964091736687312762 : ℝ) ≤ √5 ∧
    √5 ≤ (2.2360679774997896964091736687312763 : ℝ) := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem sqrt3_bounds : (1.7320508075688772935274463415058723 : ℝ) ≤ √3 ∧
    √3 ≤ (1.7320508075688772935274463415058724 : ℝ) := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem sin_pi_div_five_bounds : (0.5877852522924731291687059546390 : ℝ) ≤ sin (π / 5) ∧
    sin (π / 5) ≤ (0.5877852522924731291687059546391 : ℝ) := by
  have hs : 0 ≤ sin (π / 5) := sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (by linarith [pi_pos])
  have hsq : sin (π / 5) ^ 2 = (10 - 2 * √5) / 16 := by
    have h := sin_sq_add_cos_sq (π / 5)
    rw [cos_pi_div_five] at h
    have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith
  obtain ⟨l5, u5⟩ := sqrt5_bounds
  constructor
  · rw [← pow_le_pow_iff_left₀ (by norm_num) hs (by norm_num : (2 : ℕ) ≠ 0), hsq]
    linarith
  · rw [← pow_le_pow_iff_left₀ hs (by norm_num) (by norm_num : (2 : ℕ) ≠ 0), hsq]
    linarith

/-- `θ₁ = 2π/15`. -/
noncomputable def θ₁ : ℝ := 2 * π / 15

theorem θ₁_eq : θ₁ = π / 3 - π / 5 := by unfold θ₁; ring

theorem cos_θ₁_bounds : (0.9135454576426008955021275719 : ℝ) ≤ cos θ₁ ∧
    cos θ₁ ≤ (0.9135454576426008955021275720 : ℝ) := by
  rw [θ₁_eq, cos_sub, cos_pi_div_three, sin_pi_div_three, cos_pi_div_five]
  obtain ⟨l5, u5⟩ := sqrt5_bounds
  obtain ⟨l3, u3⟩ := sqrt3_bounds
  obtain ⟨ls, us⟩ := sin_pi_div_five_bounds
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  constructor
  · nlinarith [mul_le_mul l3 ls (by norm_num) h3]
  · nlinarith [mul_le_mul u3 us (by positivity) (by norm_num)]

theorem sin_θ₁_bounds : (0.4067366430758002077539859903 : ℝ) ≤ sin θ₁ ∧
    sin θ₁ ≤ (0.4067366430758002077539859904 : ℝ) := by
  rw [θ₁_eq, sin_sub, cos_pi_div_three, sin_pi_div_three, cos_pi_div_five]
  obtain ⟨l5, u5⟩ := sqrt5_bounds
  obtain ⟨l3, u3⟩ := sqrt3_bounds
  obtain ⟨ls, us⟩ := sin_pi_div_five_bounds
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have h5 : 0 ≤ √5 := Real.sqrt_nonneg 5
  constructor
  · nlinarith [mul_le_mul l3 l5 (by norm_num) h3]
  · nlinarith [mul_le_mul u3 u5 h5 (by norm_num)]

/-- The wedge slope bounds the tangent. -/
theorem sin_θ₁_le_wedge : sin θ₁ ≤ 57 / 128 * cos θ₁ := by
  linarith [sin_θ₁_bounds.2, cos_θ₁_bounds.1]

theorem cos_θ₁_pos : 0 < cos θ₁ := by linarith [cos_θ₁_bounds.1]

end Cayley

end
