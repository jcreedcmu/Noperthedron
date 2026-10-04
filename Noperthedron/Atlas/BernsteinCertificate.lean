module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic


@[expose] public section


/-!
# Bernstein basis

The univariate Bernstein basis polynomials and their nonnegativity on [0, 1].

(Extracted, with only what the certificates use, from the earlier snub-cube
proof attempt.)
-/

namespace Noperthedron.Atlas.BernsteinCertificate

open scoped BigOperators

def basis (degree index : ℕ) (x : ℝ) : ℝ :=
  degree.choose index * x ^ index * (1 - x) ^ (degree - index)

theorem basis_nonnegative {degree index : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ basis degree index x := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

end Noperthedron.Atlas.BernsteinCertificate

end
