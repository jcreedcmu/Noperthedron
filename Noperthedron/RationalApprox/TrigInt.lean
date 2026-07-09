import Noperthedron.RationalApprox.Basic

/-!
# Integer Horner forms of the trig partial sums

`sin_psum 13 x` and `cos_psum 13 x` on `x = xn/xd` have the exact
common-denominator forms

    sin_psum 13 x = sinPsumNum xn xd / (25! · xd²⁵)
    cos_psum 13 x = cosPsumNum xn xd / (24! · xd²⁴)

with integer Horner numerators (coefficients `25!/(2i+1)!` and `24!/(2i)!`).
`sinNum13`/`cosNum13` compute the `round13` numerators
`⌊…_psum 13 x · 10¹³⌋` as single integer floor-divisions, so under
`decide +kernel` a trig evaluation is ~40 GMP operations instead of a chain
of `Rat` normalizations on denominators up to `~10²⁰⁰`. The checkers'
integer cores read these; `sinNum13_div_eq`/`cosNum13_div_eq` connect them
to `sinℚ`/`cosℚ`.
-/

namespace RationalApprox

/-- Numerator of `sin_psum 13 (xn/xd)` over the common denominator
`25! · xd²⁵`, in Horner form over `y = xn²`, `z = xd²`. -/
def sinPsumNum (xn xd : ℤ) : ℤ :=
  let y := xn * xn
  let z := xd * xd
  xn * (15511210043330985984000000 * z ^ 12 - y * (2585201673888497664000000 * z ^ 11 - y * (129260083694424883200000 * z ^ 10 - y * (3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y * (1)))))))))))))

/-- Numerator of `cos_psum 13 (xn/xd)` over the common denominator
`24! · xd²⁴`, in Horner form over `y = xn²`, `z = xd²`. -/
def cosPsumNum (xn xd : ℤ) : ℤ :=
  let y := xn * xn
  let z := xd * xd
  620448401733239439360000 * z ^ 12 - y * (310224200866619719680000 * z ^ 11 - y * (25852016738884976640000 * z ^ 10 - y * (861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y * (1))))))))))))

/-! ### ℕ Horner cores

Same chains as `sinPsumNum`/`cosPsumNum` but over ℕ. -/

private lemma le_psum_level {y z s c' c m : ℕ} {n : ℕ} (hy : y ≤ m * z)
    (hs : s ≤ c' * z ^ n) (hc : m * c' ≤ c) : y * s ≤ c * z ^ (n + 1) := by
  calc y * s ≤ (m * z) * (c' * z ^ n) := Nat.mul_le_mul hy hs
    _ = (m * c') * z ^ (n + 1) := by ring
    _ ≤ c * z ^ (n + 1) := mul_le_mul_left hc _

/-- ℕ core of `sinPsumNum` on `y = xn²`, `z = xd²`: the same Horner chain over
ℕ. Every level is exact (no `Nat.sub` truncation) once `y ≤ 6·z` — the
coefficient ratios `c_k/c_(k+1)` are all ≥ 6 (`sinPsumNumN_cast`). ℕ literal
arithmetic reduces ~5× faster than ℤ under the kernel: no `Int.casesOn`
constructor dispatch around every op. -/
def sinPsumNumN (y z : ℕ) : ℕ :=
  15511210043330985984000000 * z ^ 12 - y * (2585201673888497664000000 * z ^ 11 - y * (129260083694424883200000 * z ^ 10 - y * (3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))))))))))

private lemma sinPsumNumN_cast {y z : ℕ} (hy : y ≤ 6 * z) :
    ((sinPsumNumN y z : ℕ) : ℤ) =
      15511210043330985984000000 * (z:ℤ) ^ 12 - y * (2585201673888497664000000 * (z:ℤ) ^ 11 - y * (129260083694424883200000 * (z:ℤ) ^ 10 - y * (3077621040343449600000 * (z:ℤ) ^ 9 - y * (42744736671436800000 * (z:ℤ) ^ 8 - y * (388588515194880000 * (z:ℤ) ^ 7 - y * (2490952020480000 * (z:ℤ) ^ 6 - y * (11861676288000 * (z:ℤ) ^ 5 - y * (43609104000 * (z:ℤ) ^ 4 - y * (127512000 * (z:ℤ) ^ 3 - y * (303600 * (z:ℤ) ^ 2 - y * (600 * (z:ℤ) - (y:ℤ)))))))))))) := by
  have m11 : y ≤ 600 * z := hy.trans (Nat.mul_le_mul (by norm_num) le_rfl)
  have t11 : 600 * z - y ≤ 600 * z ^ 1 := by rw [pow_one]; exact Nat.sub_le _ _
  have m10 : y * (600 * z - y) ≤ 303600 * z ^ 2 :=
    le_psum_level hy t11 (by norm_num)
  have t10 : 303600 * z ^ 2 - y * (600 * z - y) ≤ 303600 * z ^ 2 := Nat.sub_le _ _
  have m9 : y * (303600 * z ^ 2 - y * (600 * z - y)) ≤ 127512000 * z ^ 3 :=
    le_psum_level hy t10 (by norm_num)
  have t9 : 127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)) ≤ 127512000 * z ^ 3 := Nat.sub_le _ _
  have m8 : y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))) ≤ 43609104000 * z ^ 4 :=
    le_psum_level hy t9 (by norm_num)
  have t8 : 43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))) ≤ 43609104000 * z ^ 4 := Nat.sub_le _ _
  have m7 : y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))) ≤ 11861676288000 * z ^ 5 :=
    le_psum_level hy t8 (by norm_num)
  have t7 : 11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))) ≤ 11861676288000 * z ^ 5 := Nat.sub_le _ _
  have m6 : y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))))) ≤ 2490952020480000 * z ^ 6 :=
    le_psum_level hy t7 (by norm_num)
  have t6 : 2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))))) ≤ 2490952020480000 * z ^ 6 := Nat.sub_le _ _
  have m5 : y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))))) ≤ 388588515194880000 * z ^ 7 :=
    le_psum_level hy t6 (by norm_num)
  have t5 : 388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))))) ≤ 388588515194880000 * z ^ 7 := Nat.sub_le _ _
  have m4 : y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))))))) ≤ 42744736671436800000 * z ^ 8 :=
    le_psum_level hy t5 (by norm_num)
  have t4 : 42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))))))) ≤ 42744736671436800000 * z ^ 8 := Nat.sub_le _ _
  have m3 : y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))))))) ≤ 3077621040343449600000 * z ^ 9 :=
    le_psum_level hy t4 (by norm_num)
  have t3 : 3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))))))) ≤ 3077621040343449600000 * z ^ 9 := Nat.sub_le _ _
  have m2 : y * (3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))))))))) ≤ 129260083694424883200000 * z ^ 10 :=
    le_psum_level hy t3 (by norm_num)
  have t2 : 129260083694424883200000 * z ^ 10 - y * (3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))))))))) ≤ 129260083694424883200000 * z ^ 10 := Nat.sub_le _ _
  have m1 : y * (129260083694424883200000 * z ^ 10 - y * (3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))))))))) ≤ 2585201673888497664000000 * z ^ 11 :=
    le_psum_level hy t2 (by norm_num)
  have t1 : 2585201673888497664000000 * z ^ 11 - y * (129260083694424883200000 * z ^ 10 - y * (3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y)))))))))) ≤ 2585201673888497664000000 * z ^ 11 := Nat.sub_le _ _
  have m0 : y * (2585201673888497664000000 * z ^ 11 - y * (129260083694424883200000 * z ^ 10 - y * (3077621040343449600000 * z ^ 9 - y * (42744736671436800000 * z ^ 8 - y * (388588515194880000 * z ^ 7 - y * (2490952020480000 * z ^ 6 - y * (11861676288000 * z ^ 5 - y * (43609104000 * z ^ 4 - y * (127512000 * z ^ 3 - y * (303600 * z ^ 2 - y * (600 * z - y))))))))))) ≤ 15511210043330985984000000 * z ^ 12 :=
    le_psum_level hy t1 (by norm_num)
  unfold sinPsumNumN
  push_cast [Nat.cast_sub m0, Nat.cast_sub m1, Nat.cast_sub m2, Nat.cast_sub m3, Nat.cast_sub m4, Nat.cast_sub m5, Nat.cast_sub m6, Nat.cast_sub m7, Nat.cast_sub m8, Nat.cast_sub m9, Nat.cast_sub m10, Nat.cast_sub m11]
  ring

/-- ℕ core of `cosPsumNum` on `y = xn²`, `z = xd²`: the same Horner chain over
ℕ. Every level is exact (no `Nat.sub` truncation) once `y ≤ 2·z` — the
coefficient ratios `c_k/c_(k+1)` are all ≥ 2 (`cosPsumNumN_cast`). ℕ literal
arithmetic reduces ~5× faster than ℤ under the kernel: no `Int.casesOn`
constructor dispatch around every op. -/
def cosPsumNumN (y z : ℕ) : ℕ :=
  620448401733239439360000 * z ^ 12 - y * (310224200866619719680000 * z ^ 11 - y * (25852016738884976640000 * z ^ 10 - y * (861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))))))))))

private lemma cosPsumNumN_cast {y z : ℕ} (hy : y ≤ 2 * z) :
    ((cosPsumNumN y z : ℕ) : ℤ) =
      620448401733239439360000 * (z:ℤ) ^ 12 - y * (310224200866619719680000 * (z:ℤ) ^ 11 - y * (25852016738884976640000 * (z:ℤ) ^ 10 - y * (861733891296165888000 * (z:ℤ) ^ 9 - y * (15388105201717248000 * (z:ℤ) ^ 8 - y * (170978946685747200 * (z:ℤ) ^ 7 - y * (1295295050649600 * (z:ℤ) ^ 6 - y * (7117005772800 * (z:ℤ) ^ 5 - y * (29654190720 * (z:ℤ) ^ 4 - y * (96909120 * (z:ℤ) ^ 3 - y * (255024 * (z:ℤ) ^ 2 - y * (552 * (z:ℤ) - (y:ℤ)))))))))))) := by
  have m11 : y ≤ 552 * z := hy.trans (Nat.mul_le_mul (by norm_num) le_rfl)
  have t11 : 552 * z - y ≤ 552 * z ^ 1 := by rw [pow_one]; exact Nat.sub_le _ _
  have m10 : y * (552 * z - y) ≤ 255024 * z ^ 2 :=
    le_psum_level hy t11 (by norm_num)
  have t10 : 255024 * z ^ 2 - y * (552 * z - y) ≤ 255024 * z ^ 2 := Nat.sub_le _ _
  have m9 : y * (255024 * z ^ 2 - y * (552 * z - y)) ≤ 96909120 * z ^ 3 :=
    le_psum_level hy t10 (by norm_num)
  have t9 : 96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)) ≤ 96909120 * z ^ 3 := Nat.sub_le _ _
  have m8 : y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))) ≤ 29654190720 * z ^ 4 :=
    le_psum_level hy t9 (by norm_num)
  have t8 : 29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))) ≤ 29654190720 * z ^ 4 := Nat.sub_le _ _
  have m7 : y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))) ≤ 7117005772800 * z ^ 5 :=
    le_psum_level hy t8 (by norm_num)
  have t7 : 7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))) ≤ 7117005772800 * z ^ 5 := Nat.sub_le _ _
  have m6 : y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))))) ≤ 1295295050649600 * z ^ 6 :=
    le_psum_level hy t7 (by norm_num)
  have t6 : 1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))))) ≤ 1295295050649600 * z ^ 6 := Nat.sub_le _ _
  have m5 : y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))))) ≤ 170978946685747200 * z ^ 7 :=
    le_psum_level hy t6 (by norm_num)
  have t5 : 170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))))) ≤ 170978946685747200 * z ^ 7 := Nat.sub_le _ _
  have m4 : y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))))))) ≤ 15388105201717248000 * z ^ 8 :=
    le_psum_level hy t5 (by norm_num)
  have t4 : 15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))))))) ≤ 15388105201717248000 * z ^ 8 := Nat.sub_le _ _
  have m3 : y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))))))) ≤ 861733891296165888000 * z ^ 9 :=
    le_psum_level hy t4 (by norm_num)
  have t3 : 861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))))))) ≤ 861733891296165888000 * z ^ 9 := Nat.sub_le _ _
  have m2 : y * (861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))))))))) ≤ 25852016738884976640000 * z ^ 10 :=
    le_psum_level hy t3 (by norm_num)
  have t2 : 25852016738884976640000 * z ^ 10 - y * (861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))))))))) ≤ 25852016738884976640000 * z ^ 10 := Nat.sub_le _ _
  have m1 : y * (25852016738884976640000 * z ^ 10 - y * (861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))))))))) ≤ 310224200866619719680000 * z ^ 11 :=
    le_psum_level hy t2 (by norm_num)
  have t1 : 310224200866619719680000 * z ^ 11 - y * (25852016738884976640000 * z ^ 10 - y * (861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y)))))))))) ≤ 310224200866619719680000 * z ^ 11 := Nat.sub_le _ _
  have m0 : y * (310224200866619719680000 * z ^ 11 - y * (25852016738884976640000 * z ^ 10 - y * (861733891296165888000 * z ^ 9 - y * (15388105201717248000 * z ^ 8 - y * (170978946685747200 * z ^ 7 - y * (1295295050649600 * z ^ 6 - y * (7117005772800 * z ^ 5 - y * (29654190720 * z ^ 4 - y * (96909120 * z ^ 3 - y * (255024 * z ^ 2 - y * (552 * z - y))))))))))) ≤ 620448401733239439360000 * z ^ 12 :=
    le_psum_level hy t1 (by norm_num)
  unfold cosPsumNumN
  push_cast [Nat.cast_sub m0, Nat.cast_sub m1, Nat.cast_sub m2, Nat.cast_sub m3, Nat.cast_sub m4, Nat.cast_sub m5, Nat.cast_sub m6, Nat.cast_sub m7, Nat.cast_sub m8, Nat.cast_sub m9, Nat.cast_sub m10, Nat.cast_sub m11]
  ring


/-- `sinPsumNum` through the ℕ core (exact once `xn² ≤ 6·xd²`, i.e. `|x| ≤ √6`). -/
private lemma sinPsumNum_eq_natCore (xn xd : ℤ)
    (h : xn.natAbs * xn.natAbs ≤ 6 * (xd.natAbs * xd.natAbs)) :
    sinPsumNum xn xd =
      xn * ((sinPsumNumN (xn.natAbs * xn.natAbs) (xd.natAbs * xd.natAbs) : ℕ) : ℤ) := by
  rw [sinPsumNumN_cast h,
    (Int.natAbs_mul_self : ((xn.natAbs * xn.natAbs : ℕ) : ℤ) = xn * xn),
    (Int.natAbs_mul_self : ((xd.natAbs * xd.natAbs : ℕ) : ℤ) = xd * xd)]
  simp only [sinPsumNum]
  ring

/-- `cosPsumNum` through the ℕ core (exact once `xn² ≤ 2·xd²`, i.e. `|x| ≤ √2` —
beyond that the cosine numerator can go negative and ℕ cannot represent it). -/
private lemma cosPsumNum_eq_natCore (xn xd : ℤ)
    (h : xn.natAbs * xn.natAbs ≤ 2 * (xd.natAbs * xd.natAbs)) :
    cosPsumNum xn xd =
      ((cosPsumNumN (xn.natAbs * xn.natAbs) (xd.natAbs * xd.natAbs) : ℕ) : ℤ) := by
  rw [cosPsumNumN_cast h,
    (Int.natAbs_mul_self : ((xn.natAbs * xn.natAbs : ℕ) : ℤ) = xn * xn),
    (Int.natAbs_mul_self : ((xd.natAbs * xd.natAbs : ℕ) : ℤ) = xd * xd)]
  simp only [cosPsumNum]
  ring

private lemma floor_intCast_div_intCast (a b : ℤ) (hb : (0:ℤ) < b) :
    ⌊(a : ℚ) / (b : ℚ)⌋ = a / b := by
  have h1 : ((b.toNat : ℕ) : ℚ) = (b : ℚ) := by
    rw [show ((b.toNat : ℕ) : ℚ) = ((b.toNat : ℤ) : ℚ) from by push_cast; ring,
        Int.toNat_of_nonneg hb.le]
  rw [← h1, Rat.floor_intCast_div_natCast]
  rw [show ((b.toNat : ℕ) : ℤ) = b from Int.toNat_of_nonneg hb.le]

/-- Exact rational value of the degree-25 sine partial sum. -/
lemma sin_psum_13_eq (x : ℚ) :
    sin_psum 13 x = ((sinPsumNum x.num (x.den : ℤ) : ℤ) : ℚ)
      / ((15511210043330985984000000 * (x.den : ℤ) ^ 25 : ℤ) : ℚ) := by
  set xn := x.num with hxn
  set xd : ℤ := (x.den : ℤ) with hxd
  have hxd0 : (0:ℤ) < xd := by rw [hxd]; exact_mod_cast x.pos
  have hxdQ : ((xd : ℤ) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hxd0
  have hx : x = (xn : ℚ) / (xd : ℚ) := by
    rw [hxn, hxd]; push_cast; exact (Rat.num_div_den x).symm
  unfold sin_psum sinPsumNum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hx]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- Exact rational value of the degree-24 cosine partial sum. -/
lemma cos_psum_13_eq (x : ℚ) :
    cos_psum 13 x = ((cosPsumNum x.num (x.den : ℤ) : ℤ) : ℚ)
      / ((620448401733239439360000 * (x.den : ℤ) ^ 24 : ℤ) : ℚ) := by
  set xn := x.num with hxn
  set xd : ℤ := (x.den : ℤ) with hxd
  have hxd0 : (0:ℤ) < xd := by rw [hxd]; exact_mod_cast x.pos
  have hxdQ : ((xd : ℤ) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hxd0
  have hx : x = (xn : ℚ) / (xd : ℚ) := by
    rw [hxn, hxd]; push_cast; exact (Rat.num_div_den x).symm
  unfold cos_psum cosPsumNum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hx]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- The `round13` numerator of the sine partial sum, as a single integer
floor-division. -/
def sinNum13 (x : ℚ) : ℤ :=
  if x.num.natAbs * x.num.natAbs ≤ 6 * (x.den * x.den) then
    -- ℕ fast path (`|x| ≤ √6` — all real inputs; angles stay below ~1.6): the
    -- Horner core, the 10¹³ scale and the denominator are pure-ℕ GMP ops; only
    -- the sign factor and the final floor division touch ℤ.
    x.num * ((sinPsumNumN (x.num.natAbs * x.num.natAbs) (x.den * x.den) * 10 ^ 13 : ℕ) : ℤ)
      / ((15511210043330985984000000 * x.den ^ 25 : ℕ) : ℤ)
  else
    sinPsumNum x.num (x.den : ℤ) * 10 ^ 13 / (15511210043330985984000000 * (x.den : ℤ) ^ 25)

private lemma sinNum13_eq_old (x : ℚ) :
    sinNum13 x = sinPsumNum x.num (x.den : ℤ) * 10 ^ 13
      / (15511210043330985984000000 * (x.den : ℤ) ^ 25) := by
  unfold sinNum13
  split
  next h =>
    rw [sinPsumNum_eq_natCore x.num (x.den : ℤ) (by simpa using h)]
    congr 1
    push_cast [Int.natAbs_natCast]
    ring
  next h => rfl

/-- The `round13` numerator of the cosine partial sum. -/
def cosNum13 (x : ℚ) : ℤ :=
  if x.num.natAbs * x.num.natAbs ≤ 2 * (x.den * x.den) then
    ((cosPsumNumN (x.num.natAbs * x.num.natAbs) (x.den * x.den) * 10 ^ 13 : ℕ) : ℤ)
      / ((620448401733239439360000 * x.den ^ 24 : ℕ) : ℤ)
  else
    cosPsumNum x.num (x.den : ℤ) * 10 ^ 13 / (620448401733239439360000 * (x.den : ℤ) ^ 24)

private lemma cosNum13_eq_old (x : ℚ) :
    cosNum13 x = cosPsumNum x.num (x.den : ℤ) * 10 ^ 13
      / (620448401733239439360000 * (x.den : ℤ) ^ 24) := by
  unfold cosNum13
  split
  next h =>
    rw [cosPsumNum_eq_natCore x.num (x.den : ℤ) (by simpa using h)]
    congr 1
  next h => rfl

lemma sinNum13_eq_floor (x : ℚ) : sinNum13 x = ⌊sin_psum 13 x * 10 ^ 13⌋ := by
  have hD : (0:ℤ) < 15511210043330985984000000 * (x.den : ℤ) ^ 25 := by
    have : (0:ℤ) < (x.den : ℤ) := by exact_mod_cast x.pos
    positivity
  rw [sin_psum_13_eq, sinNum13_eq_old]
  rw [show ((sinPsumNum x.num (x.den : ℤ) : ℤ) : ℚ)
        / ((15511210043330985984000000 * (x.den : ℤ) ^ 25 : ℤ) : ℚ) * 10 ^ 13
      = ((sinPsumNum x.num (x.den : ℤ) * 10 ^ 13 : ℤ) : ℚ)
        / ((15511210043330985984000000 * (x.den : ℤ) ^ 25 : ℤ) : ℚ) from by push_cast; ring]
  rw [floor_intCast_div_intCast _ _ hD]

lemma cosNum13_eq_floor (x : ℚ) : cosNum13 x = ⌊cos_psum 13 x * 10 ^ 13⌋ := by
  have hD : (0:ℤ) < 620448401733239439360000 * (x.den : ℤ) ^ 24 := by
    have : (0:ℤ) < (x.den : ℤ) := by exact_mod_cast x.pos
    positivity
  rw [cos_psum_13_eq, cosNum13_eq_old]
  rw [show ((cosPsumNum x.num (x.den : ℤ) : ℤ) : ℚ)
        / ((620448401733239439360000 * (x.den : ℤ) ^ 24 : ℤ) : ℚ) * 10 ^ 13
      = ((cosPsumNum x.num (x.den : ℤ) * 10 ^ 13 : ℤ) : ℚ)
        / ((620448401733239439360000 * (x.den : ℤ) ^ 24 : ℤ) : ℚ) from by push_cast; ring]
  rw [floor_intCast_div_intCast _ _ hD]

/-- `sinℚ` through the integer core. -/
lemma sinNum13_div_eq (x : ℚ) : ((sinNum13 x : ℤ) : ℚ) / 10 ^ 13 = sinℚ x := by
  rw [sinNum13_eq_floor]
  rfl

/-- `cosℚ` through the integer core. -/
lemma cosNum13_div_eq (x : ℚ) : ((cosNum13 x : ℤ) : ℚ) / 10 ^ 13 = cosℚ x := by
  rw [cosNum13_eq_floor]
  rfl

end RationalApprox
