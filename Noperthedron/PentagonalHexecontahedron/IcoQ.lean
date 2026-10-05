module

public import Noperthedron.PentagonalHexecontahedron.IcoField

@[expose] public section

/-!
# The field K = ℚ(√5, sin 72°) with rational coordinates

`IcoQ` is a + b√5 + c s + d s√5 with a, b, c, d ∈ ℚ (s = sin 72°, s² = (5 + √5)/8),
the exact arithmetic of the deltoidal hexecontahedron's certificates (the
solid's coordinates in the model frame are in K, `nopert229/dh_exact.py`).
`val` is the real value; addition and multiplication are compatible with it,
and `lo`/`hi` are rational enclosures (from `IcoZ.sqrt5_bounds`, `s72_bounds`).
-/

namespace Noperthedron.PentagonalHexecontahedron

structure IcoQ where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
deriving DecidableEq, Repr

namespace IcoQ

def zero : IcoQ := ⟨0, 0, 0, 0⟩
def one : IcoQ := ⟨1, 0, 0, 0⟩
def ofRat (q : ℚ) : IcoQ := ⟨q, 0, 0, 0⟩

def add (x y : IcoQ) : IcoQ := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def neg (x : IcoQ) : IcoQ := ⟨-x.a, -x.b, -x.c, -x.d⟩
def sub (x y : IcoQ) : IcoQ := add x (neg y)
def scale (k : ℚ) (x : IcoQ) : IcoQ := ⟨k * x.a, k * x.b, k * x.c, k * x.d⟩

def mul (x y : IcoQ) : IcoQ :=
  let p := x.c * y.c + 5 * x.d * y.d
  let q := x.c * y.d + x.d * y.c
  ⟨x.a * y.a + 5 * x.b * y.b + (5 * p + 5 * q) / 8,
   x.a * y.b + x.b * y.a + (p + 5 * q) / 8,
   x.a * y.c + 5 * x.b * y.d + x.c * y.a + 5 * x.d * y.b,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩

instance : Add IcoQ := ⟨add⟩
instance : Neg IcoQ := ⟨neg⟩
instance : Sub IcoQ := ⟨sub⟩
instance : Mul IcoQ := ⟨mul⟩
instance : Zero IcoQ := ⟨zero⟩
instance : One IcoQ := ⟨one⟩

/-- The value in ℝ. -/
noncomputable def val (x : IcoQ) : ℝ :=
  x.a + x.b * IcoZ.sqrt5 + x.c * IcoZ.s72 + x.d * IcoZ.sqrt5 * IcoZ.s72

@[simp] theorem val_add (x y : IcoQ) : val (x + y) = val x + val y := by
  show val (add x y) = _
  simp only [val, add]; push_cast; ring

@[simp] theorem val_neg (x : IcoQ) : val (-x) = -val x := by
  show val (neg x) = _
  simp only [val, neg]; push_cast; ring

@[simp] theorem val_sub (x y : IcoQ) : val (x - y) = val x - val y := by
  show val (add x (neg y)) = _
  simp only [val, add, neg]; push_cast; ring

@[simp] theorem val_scale (k : ℚ) (x : IcoQ) : val (scale k x) = k * val x := by
  simp only [val, scale]; push_cast; ring

@[simp] theorem val_mul (x y : IcoQ) : val (x * y) = val x * val y := by
  show val (mul x y) = _
  have hr := IcoZ.sqrt5_sq
  have hs := IcoZ.s72_sq
  simp only [val, mul]
  push_cast
  linear_combination
    (-((x.b : ℝ) * y.b + ((x.b : ℝ) * y.d + x.d * y.b) * IcoZ.s72 + (x.d : ℝ) * y.d * IcoZ.s72 ^ 2 +
        ((x.c : ℝ) * y.d + x.d * y.c) / 8)) * hr +
    (-(((x.c : ℝ) * y.c + 5 * x.d * y.d) + ((x.c : ℝ) * y.d + x.d * y.c) * IcoZ.sqrt5)) * hs

@[simp] theorem val_zero : val 0 = 0 := by
  show val zero = 0
  simp [val, zero]

@[simp] theorem val_one : val 1 = 1 := by
  show val one = 1
  simp [val, one]

@[simp] theorem val_ofRat (q : ℚ) : val (ofRat q) = q := by simp [val, ofRat]

/-! ### Rational enclosures -/

def loMul (k l u : ℚ) : ℚ := if 0 ≤ k then k * l else k * u
def hiMul (k l u : ℚ) : ℚ := if 0 ≤ k then k * u else k * l

theorem loMul_le (k : ℚ) {l u : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hu : t ≤ u) :
    ((loMul k l u : ℚ) : ℝ) ≤ k * t := by
  unfold loMul
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hu (by exact_mod_cast (le_of_lt (not_le.mp hk)))

theorem le_hiMul (k : ℚ) {l u : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hu : t ≤ u) :
    k * t ≤ ((hiMul k l u : ℚ) : ℝ) := by
  unfold hiMul
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hu (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hl (by exact_mod_cast (le_of_lt (not_le.mp hk)))

def lo (x : IcoQ) : ℚ :=
  x.a + loMul x.b IcoZ.sqrt5Lo IcoZ.sqrt5Hi + loMul x.c IcoZ.s72Lo IcoZ.s72Hi +
    loMul x.d (IcoZ.sqrt5Lo * IcoZ.s72Lo) (IcoZ.sqrt5Hi * IcoZ.s72Hi)

def hi (x : IcoQ) : ℚ :=
  x.a + hiMul x.b IcoZ.sqrt5Lo IcoZ.sqrt5Hi + hiMul x.c IcoZ.s72Lo IcoZ.s72Hi +
    hiMul x.d (IcoZ.sqrt5Lo * IcoZ.s72Lo) (IcoZ.sqrt5Hi * IcoZ.s72Hi)

theorem lo_le_val (x : IcoQ) : (lo x : ℝ) ≤ val x := by
  obtain ⟨h5lo, h5hi⟩ := IcoZ.sqrt5_bounds
  obtain ⟨hslo, hshi⟩ := IcoZ.s72_bounds
  obtain ⟨hplo, hphi⟩ := IcoZ.prod_bounds
  have hb := loMul_le x.b h5lo h5hi
  have hc := loMul_le x.c hslo hshi
  have hd := loMul_le x.d hplo hphi
  simp only [lo, val]
  push_cast at hb hc hd ⊢
  nlinarith

theorem val_le_hi (x : IcoQ) : val x ≤ (hi x : ℝ) := by
  obtain ⟨h5lo, h5hi⟩ := IcoZ.sqrt5_bounds
  obtain ⟨hslo, hshi⟩ := IcoZ.s72_bounds
  obtain ⟨hplo, hphi⟩ := IcoZ.prod_bounds
  have hb := le_hiMul x.b h5lo h5hi
  have hc := le_hiMul x.c hslo hshi
  have hd := le_hiMul x.d hplo hphi
  simp only [hi, val]
  push_cast at hb hc hd ⊢
  nlinarith

end IcoQ

end Noperthedron.PentagonalHexecontahedron
