import Noperthedron.RationalApprox.Basic
import Noperthedron.Nopert

/-!
# Rational approximate noperthedron vertices

Computable rational approximations of the 90 noperthedron vertices,
using `sinℚ`/`cosℚ` evaluated at a rational approximation of `2πk/15`.

## Architecture

The real vertex `nopertPt k ℓ i = (-1)^ℓ • RzL(2πk/15)(Cpt i)` uses
transcendental `sin(2πk/15)` and `cos(2πk/15)`.

The approximate vertex replaces these with:
- `sinℚ(2 * piApprox * k / 15 : ℚ)` — 13-term Taylor polynomial at rational π
- `cosℚ(2 * piApprox * k / 15 : ℚ)` — same

This is fully computable over ℚ. The approximation error has two parts:
1. `|sin(x) - sinℚ(x)| ≤ κ/7` from Taylor remainder (`sinℚ_approx'`)
2. `|sinℚ(2πk/15) - sinℚ(2·piApprox·k/15)| ≤ Lip · |π - piApprox|`
   where Lip ≤ 2 (polynomial Lipschitz) and |π - piApprox| < 10⁻¹⁹

Total vertex error: bounded, well within κ.
-/

namespace Solution

open RationalApprox

/-! ### Rational π approximation -/

/-- 20-digit rational approximation of π.
    |π - piApprox| < 10⁻¹⁹. -/
def piApprox : ℚ := 31415926535897932385 / 10^19

/-! ### Computable trig at rotation angles -/

/-- sinℚ evaluated at the rational approximation of `2πk/15`. -/
def sinQAt (k : ℕ) : ℚ := sinℚ (2 * piApprox * k / 15)

/-- cosℚ evaluated at the rational approximation of `2πk/15`. -/
def cosQAt (k : ℕ) : ℚ := cosℚ (2 * piApprox * k / 15)

/-! ### Computable approximate vertices -/

/-- The three basis vertices as ℚ³ vectors. -/
def basisQ : Fin 3 → (Fin 3 → ℚ)
  | 0 => Nopert.C1
  | 1 => Nopert.C2
  | 2 => Nopert.C3

/-- Approximate Rz rotation applied to a rational 3-vector. -/
def rzApproxQ (k : ℕ) (v : Fin 3 → ℚ) : Fin 3 → ℚ :=
  let c := cosQAt k
  let s := sinQAt k
  fun
  | 0 => c * v 0 - s * v 1
  | 1 => s * v 0 + c * v 1
  | 2 => v 2

/-- Approximate nopert vertex (ℓ=0 only; ℓ=1 is negation). -/
def approxNopertVertQ (k : ℕ) (i : Fin 3) : Fin 3 → ℚ :=
  rzApproxQ k (basisQ i)

/-- Approximate nopert vertex with parity. -/
def approxNopertVertParQ (k ℓ : ℕ) (i : Fin 3) : Fin 3 → ℚ :=
  let v := approxNopertVertQ k i
  if ℓ % 2 = 0 then v else fun j => -(v j)

/-- Look up approximate vertex by linear index (matching Row.indexPoint's decoding). -/
def approxVertexByIndex (idx : ℕ) : Fin 3 → ℚ :=
  let i := (idx % 45) / 15  -- decodeI
  let k := idx % 15          -- decodeK
  let ℓ := idx / 45          -- decodeL
  approxNopertVertParQ k ℓ ⟨i, by omega⟩

end Solution
