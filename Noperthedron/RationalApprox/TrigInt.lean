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
  sinPsumNum x.num (x.den : ℤ) * 10 ^ 13 / (15511210043330985984000000 * (x.den : ℤ) ^ 25)

/-- The `round13` numerator of the cosine partial sum. -/
def cosNum13 (x : ℚ) : ℤ :=
  cosPsumNum x.num (x.den : ℤ) * 10 ^ 13 / (620448401733239439360000 * (x.den : ℤ) ^ 24)

lemma sinNum13_eq_floor (x : ℚ) : sinNum13 x = ⌊sin_psum 13 x * 10 ^ 13⌋ := by
  have hD : (0:ℤ) < 15511210043330985984000000 * (x.den : ℤ) ^ 25 := by
    have : (0:ℤ) < (x.den : ℤ) := by exact_mod_cast x.pos
    positivity
  rw [sin_psum_13_eq, sinNum13]
  rw [show ((sinPsumNum x.num (x.den : ℤ) : ℤ) : ℚ)
        / ((15511210043330985984000000 * (x.den : ℤ) ^ 25 : ℤ) : ℚ) * 10 ^ 13
      = ((sinPsumNum x.num (x.den : ℤ) * 10 ^ 13 : ℤ) : ℚ)
        / ((15511210043330985984000000 * (x.den : ℤ) ^ 25 : ℤ) : ℚ) from by push_cast; ring]
  rw [floor_intCast_div_intCast _ _ hD]

lemma cosNum13_eq_floor (x : ℚ) : cosNum13 x = ⌊cos_psum 13 x * 10 ^ 13⌋ := by
  have hD : (0:ℤ) < 620448401733239439360000 * (x.den : ℤ) ^ 24 := by
    have : (0:ℤ) < (x.den : ℤ) := by exact_mod_cast x.pos
    positivity
  rw [cos_psum_13_eq, cosNum13]
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
