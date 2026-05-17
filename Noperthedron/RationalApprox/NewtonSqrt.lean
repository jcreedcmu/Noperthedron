import Noperthedron.RationalApprox.Basic

/-!
# Newton-based square root approximations

Constructs `UpperSqrt` and `LowerSqrt` via Newton iteration on ℝ,
with a parallel ℚ computation for the rationality witness.

## Strategy

- **UpperSqrt**: `f x = newtonSqrtUpper 20 x` — 20 Newton iterations from `x + 1`
- **LowerSqrt**: `f x = x / newtonSqrtUpper 20 x` — divide by upper bound

Upper bound follows from AM-GM at each step: `(q + x/q)/2 ≥ √x`.
Lower bound follows from `x / upper ≤ x / √x = √x`.
-/

namespace RationalApprox

open Real

/-! ### ℚ-level Newton iteration (computable) -/

/-- k iterations of Newton's method for √x on ℚ, starting from x + 1. -/
def newtonSqrtQ : ℕ → ℚ → ℚ
  | 0, x => x + 1
  | n + 1, x => let q := newtonSqrtQ n x; (q + x / q) / 2

/-! ### ℝ-level Newton iteration (noncomputable) -/

noncomputable section

/-- k iterations of Newton's method for √x on ℝ, starting from x + 1. -/
def newtonSqrtUpper : ℕ → ℝ → ℝ
  | 0, x => x + 1
  | n + 1, x => let q := newtonSqrtUpper n x; (q + x / q) / 2

/-! ### Positivity -/

theorem newtonSqrtUpper_pos (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 < newtonSqrtUpper k x := by
  induction k with
  | zero => simp [newtonSqrtUpper]; linarith
  | succ n ih =>
    simp only [newtonSqrtUpper]
    have hq := ih
    have hxq : 0 ≤ x / newtonSqrtUpper n x := div_nonneg hx (le_of_lt hq)
    linarith

/-! ### Upper bound: √x ≤ newtonSqrtUpper k x -/

theorem sqrt_le_newtonSqrtUpper (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    √x ≤ newtonSqrtUpper k x := by
  induction k with
  | zero =>
    -- √x ≤ x + 1 ↔ x ≤ (x + 1)²
    simp only [newtonSqrtUpper]
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [sq_nonneg x]
  | succ n ih =>
    -- AM-GM: (q + x/q)/2 ≥ √x, using (q - √x)² ≥ 0
    simp only [newtonSqrtUpper]
    have hq := newtonSqrtUpper_pos n x hx
    have hsq : 0 ≤ (newtonSqrtUpper n x - √x) ^ 2 := sq_nonneg _
    have hsqrt_sq : √x ^ 2 = x := Real.sq_sqrt hx
    -- Expand (q - √x)² ≥ 0 → q² - 2q√x + x ≥ 0 → q + x/q ≥ 2√x
    have h1 : newtonSqrtUpper n x + x / newtonSqrtUpper n x ≥ 2 * √x := by
      rw [ge_iff_le, ← sub_nonneg]
      have : newtonSqrtUpper n x + x / newtonSqrtUpper n x - 2 * √x =
          (newtonSqrtUpper n x - √x) ^ 2 / newtonSqrtUpper n x := by
        field_simp
        nlinarith [hsqrt_sq]
      rw [this]
      positivity
    linarith

/-! ### ℚ correspondence -/

theorem newtonSqrtQ_pos (k : ℕ) (x : ℚ) (hx : 0 ≤ x) :
    0 < newtonSqrtQ k x := by
  induction k with
  | zero => simp [newtonSqrtQ]; linarith
  | succ n ih =>
    simp only [newtonSqrtQ]
    have hq := ih
    have hxq : 0 ≤ x / newtonSqrtQ n x := div_nonneg hx (le_of_lt hq)
    linarith

theorem newtonSqrtUpper_eq_cast (k : ℕ) (x : ℚ) (hx : 0 ≤ x) :
    newtonSqrtUpper k (x : ℝ) = (newtonSqrtQ k x : ℝ) := by
  induction k with
  | zero => simp [newtonSqrtUpper, newtonSqrtQ]
  | succ n ih =>
    simp only [newtonSqrtUpper, newtonSqrtQ]
    rw [ih]
    have hq : (newtonSqrtQ n x : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast newtonSqrtQ_pos n x hx)
    rw [Rat.cast_div, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]

/-! ### Construction of UpperSqrt and LowerSqrt -/

private def numIters : ℕ := 20

/-- Upper sqrt approximation via 20 Newton iterations. -/
noncomputable def newtonUpperSqrt : UpperSqrt where
  f x := newtonSqrtUpper numIters x
  rational x hx := by
    exact ⟨newtonSqrtQ numIters x, newtonSqrtUpper_eq_cast numIters x hx⟩
  bound x hx := sqrt_le_newtonSqrtUpper numIters x hx

/-- Lower sqrt approximation: x / (Newton upper bound). -/
noncomputable def newtonLowerSqrt : LowerSqrt where
  f x := x / newtonSqrtUpper numIters x
  rational x hx := by
    refine ⟨x / newtonSqrtQ numIters x, ?_⟩
    rw [newtonSqrtUpper_eq_cast numIters x hx]
    push_cast [ne_of_gt (newtonSqrtQ_pos numIters x hx)]
    rfl
  bound x hx := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hup := newtonSqrtUpper_pos numIters x hx
      have hsq := sqrt_le_newtonSqrtUpper numIters x hx
      rw [div_le_iff₀ hup]
      calc x = √x * √x := by rw [Real.mul_self_sqrt hx]
        _ ≤ √x * newtonSqrtUpper numIters x :=
              mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)

end

end RationalApprox
