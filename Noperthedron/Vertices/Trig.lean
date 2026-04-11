import Mathlib.Data.Rat.Defs

namespace Noperthedron

/-! ## Computable sine and cosine (Taylor polynomials in Horner form)

`sinQ x` computes the degree-25 Taylor polynomial of sin:
  x · (1 − x²/(2·3) · (1 − x²/(4·5) · ⋯ (1 − x²/(24·25))))

`cosQ x` computes the degree-24 Taylor polynomial of cos:
  1 − x²/(1·2) · (1 − x²/(3·4) · ⋯ (1 − x²/(23·24)))

These are mathematically identical to `sin_psum 13` and `cos_psum 13`
in `RationalApprox/Basic.lean`, but manifestly computable.
-/

def sinQ (x : ℚ) : ℚ :=
  let x2 := x * x
  x * (1 - x2 / (2*3) * (1 - x2 / (4*5) * (1 - x2 / (6*7) *
      (1 - x2 / (8*9) * (1 - x2 / (10*11) * (1 - x2 / (12*13) *
      (1 - x2 / (14*15) * (1 - x2 / (16*17) * (1 - x2 / (18*19) *
      (1 - x2 / (20*21) * (1 - x2 / (22*23) * (1 - x2 / (24*25)
      ))))))))))))

def cosQ (x : ℚ) : ℚ :=
  let x2 := x * x
  1 - x2 / (1*2) * (1 - x2 / (3*4) * (1 - x2 / (5*6) *
     (1 - x2 / (7*8) * (1 - x2 / (9*10) * (1 - x2 / (11*12) *
     (1 - x2 / (13*14) * (1 - x2 / (15*16) * (1 - x2 / (17*18) *
     (1 - x2 / (19*20) * (1 - x2 / (21*22) * (1 - x2 / (23*24)
     )))))))))))
