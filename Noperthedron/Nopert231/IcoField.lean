module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The field K = ℚ(√5, sin 72°), in integer coordinates

Every rotation of the icosahedral group, written in the snub dodecahedron's
5-fold frame (z a 5-fold axis, x a 2-fold axis; nopert229/notes/S.md §2.2),
has entries in K = ℚ(√5, s), where s = sin 72° and s² = (5 + √5)/8. K has
degree 4 over ℚ with basis 1, √5, s, s√5.

In that frame every entry is an *integer* combination of the basis divided by
20. So `IcoZ` stores four integers and `IcoZ.val` reads them as
`a + b √5 + c s + d s √5` (without the 1/20); `IcoZ.mul8` multiplies exactly
up to the factor 8 that s² introduces. Integer arithmetic (no `Rat`
normalization) keeps the kernel's decided group computations fast:
IcoGroup.lean decides the 180 generator products in seconds.

`M3` is a 3 × 3 matrix of `IcoZ` with explicit fields, and `M3.toMatrix` its
real matrix of values.
-/

namespace Noperthedron.Nopert231

open scoped Matrix

/-- `a + b √5 + c s + d s √5` with integer coordinates, s = sin 72°. -/
structure IcoZ where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

namespace IcoZ

def add (x y : IcoZ) : IcoZ := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

def scale (k : Int) (x : IcoZ) : IcoZ := ⟨k * x.a, k * x.b, k * x.c, k * x.d⟩

/-- `8 x y`, which is integral: s² = (5 + √5)/8. -/
def mul8 (x y : IcoZ) : IcoZ :=
  let p := x.c * y.c + 5 * x.d * y.d
  let q := x.c * y.d + x.d * y.c
  ⟨8 * (x.a * y.a + 5 * x.b * y.b) + 5 * p + 5 * q,
   8 * (x.a * y.b + x.b * y.a) + p + 5 * q,
   8 * (x.a * y.c + 5 * x.b * y.d + x.c * y.a + 5 * x.d * y.b),
   8 * (x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a)⟩

/-- √5. -/
noncomputable def sqrt5 : ℝ := Real.sqrt 5

/-- s = sin 72° = √((5 + √5)/8). -/
noncomputable def s72 : ℝ := Real.sqrt ((5 + sqrt5) / 8)

theorem sqrt5_nonneg : 0 ≤ sqrt5 := Real.sqrt_nonneg _

theorem sqrt5_sq : sqrt5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem s72_nonneg : 0 ≤ s72 := Real.sqrt_nonneg _

theorem s72_sq : s72 ^ 2 = (5 + sqrt5) / 8 :=
  Real.sq_sqrt (by have := sqrt5_nonneg; positivity)

/-- The value in ℝ. -/
noncomputable def val (x : IcoZ) : ℝ :=
  x.a + x.b * sqrt5 + x.c * s72 + x.d * sqrt5 * s72

@[simp] theorem val_add (x y : IcoZ) : val (add x y) = val x + val y := by
  simp only [val, add]; push_cast; ring

@[simp] theorem val_scale (k : Int) (x : IcoZ) : val (scale k x) = k * val x := by
  simp only [val, scale]; push_cast; ring

@[simp] theorem val_mul8 (x y : IcoZ) : val (mul8 x y) = 8 * (val x * val y) := by
  have hr := sqrt5_sq
  have hs := s72_sq
  simp only [val, mul8]
  push_cast
  linear_combination
    (-8 * ((x.b : ℝ) * y.b + ((x.b : ℝ) * y.d + x.d * y.b) * s72 + (x.d : ℝ) * y.d * s72 ^ 2 +
        ((x.c : ℝ) * y.d + x.d * y.c) / 8)) * hr +
    (-8 * (((x.c : ℝ) * y.c + 5 * x.d * y.d) + ((x.c : ℝ) * y.d + x.d * y.c) * sqrt5)) * hs

@[simp] theorem val_mk_int (a : Int) : val ⟨a, 0, 0, 0⟩ = a := by simp [val]

/-! ### Rational enclosures of values -/

def sqrt5Lo : ℚ := 22360679774997896964091736 / 10^25
def sqrt5Hi : ℚ := 22360679774997896964091737 / 10^25
def s72Lo : ℚ := 9510565162951535721164393 / 10^25
def s72Hi : ℚ := 9510565162951535721164394 / 10^25

theorem sqrt5_bounds : (sqrt5Lo : ℝ) ≤ sqrt5 ∧ sqrt5 ≤ sqrt5Hi := by
  have h0 := sqrt5_nonneg
  have hsq := sqrt5_sq
  constructor
  · nlinarith [sq_nonneg (sqrt5 - sqrt5Lo), show (sqrt5Lo : ℝ) ^ 2 ≤ 5 by norm_num [sqrt5Lo],
      show (0 : ℝ) ≤ sqrt5Lo by norm_num [sqrt5Lo]]
  · nlinarith [sq_nonneg (sqrt5 - sqrt5Hi), show (5 : ℝ) ≤ (sqrt5Hi : ℝ) ^ 2 by norm_num [sqrt5Hi],
      show (0 : ℝ) ≤ sqrt5Hi by norm_num [sqrt5Hi]]

theorem s72_bounds : (s72Lo : ℝ) ≤ s72 ∧ s72 ≤ s72Hi := by
  obtain ⟨h5lo, h5hi⟩ := sqrt5_bounds
  have h0 := s72_nonneg
  have hsq := s72_sq
  have hlo : (s72Lo : ℝ) ^ 2 ≤ (5 + sqrt5Lo) / 8 := by norm_num [s72Lo, sqrt5Lo]
  have hhi : (5 + sqrt5Hi) / 8 ≤ (s72Hi : ℝ) ^ 2 := by norm_num [s72Hi, sqrt5Hi]
  constructor
  · nlinarith [sq_nonneg (s72 - s72Lo), show (0 : ℝ) ≤ s72Lo by norm_num [s72Lo]]
  · nlinarith [sq_nonneg (s72 - s72Hi), show (0 : ℝ) ≤ s72Hi by norm_num [s72Hi]]

/-- A lower bound for `k t` when `l ≤ t ≤ u`. -/
def loMul (k : Int) (l u : ℚ) : ℚ := if 0 ≤ k then k * l else k * u

/-- An upper bound for `k t` when `l ≤ t ≤ u`. -/
def hiMul (k : Int) (l u : ℚ) : ℚ := if 0 ≤ k then k * u else k * l

theorem loMul_le (k : Int) {l u : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hu : t ≤ u) :
    (loMul k l u : ℝ) ≤ k * t := by
  unfold loMul
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hu (by exact_mod_cast (le_of_lt (not_le.mp hk)))

theorem le_hiMul (k : Int) {l u : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hu : t ≤ u) :
    (k : ℝ) * t ≤ hiMul k l u := by
  unfold hiMul
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hu (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hl (by exact_mod_cast (le_of_lt (not_le.mp hk)))

def lo (x : IcoZ) : ℚ :=
  x.a + loMul x.b sqrt5Lo sqrt5Hi + loMul x.c s72Lo s72Hi +
    loMul x.d (sqrt5Lo * s72Lo) (sqrt5Hi * s72Hi)

def hi (x : IcoZ) : ℚ :=
  x.a + hiMul x.b sqrt5Lo sqrt5Hi + hiMul x.c s72Lo s72Hi +
    hiMul x.d (sqrt5Lo * s72Lo) (sqrt5Hi * s72Hi)

theorem prod_bounds : ((sqrt5Lo * s72Lo : ℚ) : ℝ) ≤ sqrt5 * s72 ∧
    sqrt5 * s72 ≤ ((sqrt5Hi * s72Hi : ℚ) : ℝ) := by
  obtain ⟨h5lo, h5hi⟩ := sqrt5_bounds
  obtain ⟨hslo, hshi⟩ := s72_bounds
  have h5 : (0 : ℝ) ≤ sqrt5Lo := by norm_num [sqrt5Lo]
  have hs : (0 : ℝ) ≤ s72Lo := by norm_num [s72Lo]
  push_cast
  exact ⟨mul_le_mul h5lo hslo hs (by linarith), mul_le_mul h5hi hshi (by linarith) (by linarith)⟩

theorem lo_le_val (x : IcoZ) : (lo x : ℝ) ≤ val x := by
  obtain ⟨h5lo, h5hi⟩ := sqrt5_bounds
  obtain ⟨hslo, hshi⟩ := s72_bounds
  obtain ⟨hplo, hphi⟩ := prod_bounds
  have hb := loMul_le x.b h5lo h5hi
  have hc := loMul_le x.c hslo hshi
  have hd := loMul_le x.d hplo hphi
  simp only [lo, val]
  push_cast at hb hc hd ⊢
  nlinarith

theorem val_le_hi (x : IcoZ) : val x ≤ (hi x : ℝ) := by
  obtain ⟨h5lo, h5hi⟩ := sqrt5_bounds
  obtain ⟨hslo, hshi⟩ := s72_bounds
  obtain ⟨hplo, hphi⟩ := prod_bounds
  have hb := le_hiMul x.b h5lo h5hi
  have hc := le_hiMul x.c hslo hshi
  have hd := le_hiMul x.d hplo hphi
  simp only [hi, val]
  push_cast at hb hc hd ⊢
  nlinarith

end IcoZ

/-- A 3 × 3 matrix over `IcoZ`, row-major fields. -/
structure M3 where
  m00 : IcoZ
  m01 : IcoZ
  m02 : IcoZ
  m10 : IcoZ
  m11 : IcoZ
  m12 : IcoZ
  m20 : IcoZ
  m21 : IcoZ
  m22 : IcoZ
deriving DecidableEq, Repr

namespace M3

open IcoZ

def entry (A : M3) : Fin 3 → Fin 3 → IcoZ :=
  ![![A.m00, A.m01, A.m02], ![A.m10, A.m11, A.m12], ![A.m20, A.m21, A.m22]]

/-- `8 (u · v)` for rows/columns given entrywise. -/
def dot8 (a0 a1 a2 b0 b1 b2 : IcoZ) : IcoZ :=
  add (add (mul8 a0 b0) (mul8 a1 b1)) (mul8 a2 b2)

/-- `8 A B`. -/
def mul8 (A B : M3) : M3 :=
  ⟨dot8 A.m00 A.m01 A.m02 B.m00 B.m10 B.m20, dot8 A.m00 A.m01 A.m02 B.m01 B.m11 B.m21,
   dot8 A.m00 A.m01 A.m02 B.m02 B.m12 B.m22,
   dot8 A.m10 A.m11 A.m12 B.m00 B.m10 B.m20, dot8 A.m10 A.m11 A.m12 B.m01 B.m11 B.m21,
   dot8 A.m10 A.m11 A.m12 B.m02 B.m12 B.m22,
   dot8 A.m20 A.m21 A.m22 B.m00 B.m10 B.m20, dot8 A.m20 A.m21 A.m22 B.m01 B.m11 B.m21,
   dot8 A.m20 A.m21 A.m22 B.m02 B.m12 B.m22⟩

def scale (k : Int) (A : M3) : M3 :=
  ⟨A.m00.scale k, A.m01.scale k, A.m02.scale k, A.m10.scale k, A.m11.scale k,
   A.m12.scale k, A.m20.scale k, A.m21.scale k, A.m22.scale k⟩

def add (A B : M3) : M3 :=
  ⟨A.m00.add B.m00, A.m01.add B.m01, A.m02.add B.m02, A.m10.add B.m10, A.m11.add B.m11,
   A.m12.add B.m12, A.m20.add B.m20, A.m21.add B.m21, A.m22.add B.m22⟩

def transpose (A : M3) : M3 :=
  ⟨A.m00, A.m10, A.m20, A.m01, A.m11, A.m21, A.m02, A.m12, A.m22⟩

def zero : M3 := let z : IcoZ := ⟨0, 0, 0, 0⟩; ⟨z, z, z, z, z, z, z, z, z⟩

/-- `k I`. -/
def scalar (k : Int) : M3 :=
  let z : IcoZ := ⟨0, 0, 0, 0⟩
  let d : IcoZ := ⟨k, 0, 0, 0⟩
  ⟨d, z, z, z, d, z, z, z, d⟩

/-- `64 det A`. -/
def det64 (A : M3) : IcoZ :=
  let t (x y z : IcoZ) := IcoZ.mul8 (IcoZ.mul8 x y) z
  IcoZ.add (IcoZ.add (IcoZ.add (IcoZ.add (IcoZ.add (t A.m00 A.m11 A.m22)
    ((t A.m00 A.m12 A.m21).scale (-1))) ((t A.m01 A.m10 A.m22).scale (-1)))
    (t A.m01 A.m12 A.m20)) (t A.m02 A.m10 A.m21)) ((t A.m02 A.m11 A.m20).scale (-1))

/-- The real matrix of values. -/
noncomputable def toMatrix (A : M3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => val (A.entry i j)

theorem toMatrix_mul8 (A B : M3) :
    toMatrix (mul8 A B) = (8 : ℝ) • (toMatrix A * toMatrix B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, entry, mul8, dot8, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem toMatrix_scale (k : Int) (A : M3) : toMatrix (scale k A) = (k : ℝ) • toMatrix A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, entry, scale]

theorem toMatrix_add (A B : M3) : toMatrix (add A B) = toMatrix A + toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, entry, add]

theorem toMatrix_transpose (A : M3) : toMatrix (transpose A) = (toMatrix A)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, entry, transpose]

theorem toMatrix_zero : toMatrix zero = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, entry, zero, val]

theorem toMatrix_scalar (k : Int) : toMatrix (scalar k) = (k : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, entry, scalar, val]

theorem val_det64 (A : M3) : val (det64 A) = 64 * (toMatrix A).det := by
  simp [det64, toMatrix, entry, Matrix.det_fin_three]
  ring

end M3

end Noperthedron.Nopert231
