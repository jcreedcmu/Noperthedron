module

public import Cayley.Checker.Geometry
public import Mathlib

@[expose] public section

/-!
# Real values of the checker's dyadic numbers
-/

namespace Cayley

open scoped Matrix

/-- The real value of `⟨m, e⟩ = m / 2^e`. -/
noncomputable def D (q : QI) : ℝ := q.m / 2 ^ q.e

@[simp] theorem D_mk (m : ℤ) (e : ℕ) : D ⟨m, e⟩ = m / 2 ^ e := rfl

theorem QI.pow2_eq (k : ℕ) : QI.pow2 k = 2 ^ k := by simp [QI.pow2]

@[simp] theorem D_add (a b : QI) : D (a + b) = D a + D b := by
  change D (QI.add a b) = _
  unfold QI.add
  split_ifs with h
  · simp only [D, QI.pow2_eq]
    push_cast
    rw [show (2 : ℝ) ^ b.e = 2 ^ a.e * 2 ^ (b.e - a.e) by rw [← pow_add]; congr 1; omega]
    field_simp
  · simp only [D, QI.pow2_eq]
    push_cast
    rw [show (2 : ℝ) ^ a.e = 2 ^ b.e * 2 ^ (a.e - b.e) by rw [← pow_add]; congr 1; omega]
    field_simp

@[simp] theorem D_mul (a b : QI) : D (a * b) = D a * D b := by
  change D (QI.mul a b) = _
  simp only [QI.mul, D, pow_add]; push_cast; field_simp

@[simp] theorem D_neg (a : QI) : D (-a) = -D a := by
  change D (QI.neg a) = _
  simp only [QI.neg, D]; push_cast; ring

@[simp] theorem D_sub (a b : QI) : D (a - b) = D a - D b := by
  change D (QI.add a (QI.neg b)) = _
  rw [show QI.add a (QI.neg b) = a + -b from rfl, D_add, D_neg]; ring

@[simp] theorem D_ofNat' (n : ℕ) : D (OfNat.ofNat n : QI) = n := by
  change D ⟨n, 0⟩ = _; simp

@[simp] theorem D_zero : D (0 : QI) = 0 := by change D ⟨0, 0⟩ = _; simp
@[simp] theorem D_one : D (1 : QI) = 1 := by change D ⟨1, 0⟩ = _; simp

theorem D_errε : D errε = 1 / 2 ^ 60 := by simp [errε]

@[simp] theorem D_intCast (n : ℤ) : D (n : QI) = n := by
  change D ⟨n, 0⟩ = _; simp

theorem D_le_iff (a b : QI) : D a ≤ D b ↔ a ≤ b := by
  change _ ↔ a.m * QI.pow2 b.e ≤ b.m * QI.pow2 a.e
  rw [QI.pow2_eq, QI.pow2_eq, D, D, div_le_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> exact_mod_cast h

theorem D_lt_iff (a b : QI) : D a < D b ↔ a < b := by
  change _ ↔ a.m * QI.pow2 b.e < b.m * QI.pow2 a.e
  rw [QI.pow2_eq, QI.pow2_eq, D, D, div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> exact_mod_cast h

theorem D_d80 (m : ℤ) : D (d80 m) = m / 2 ^ 80 := rfl

/-- Real vector of a constant `V3`. -/
noncomputable def V3.toR (v : V3 QI) : Fin 3 → ℝ := ![D v.x, D v.y, D v.z]

/-- Real matrix of a constant `M3`. -/
noncomputable def M3.toR (m : M3 QI) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![D m.a00, D m.a01, D m.a02; D m.a10, D m.a11, D m.a12; D m.a20, D m.a21, D m.a22]

/-- The cross product of real vectors. -/
def crossR (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

end Cayley

end
