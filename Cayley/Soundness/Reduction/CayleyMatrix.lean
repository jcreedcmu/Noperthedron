module
-- Ported from NopertTriakisTetrahedron (Apache-2.0): Noperts/Cayley.lean

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Noperthedron.Basic

@[expose] public section

/-!
# Cayley coordinates for three-dimensional rotations

The vector `(x, y, z)` represents the unit quaternion proportional to
`(1, x, y, z)`.  Unlike Euler coordinates, the resulting rotation matrix is
rational in the three parameters.  These coordinates cover exactly the
rotations without angle `pi`; in particular they cover every rotation whose
trace is nonnegative.
-/

namespace Cayley

open scoped Matrix

/-- The positive denominator in the three-dimensional Cayley transform. -/
def cayleyDenom (x y z : ℝ) : ℝ := 1 + x ^ 2 + y ^ 2 + z ^ 2

theorem cayleyDenom_pos (x y z : ℝ) : 0 < cayleyDenom x y z := by
  unfold cayleyDenom
  positivity

theorem cayleyDenom_ne (x y z : ℝ) : cayleyDenom x y z ≠ 0 :=
  ne_of_gt (cayleyDenom_pos x y z)

/-- Polynomial numerator of the Cayley rotation, defined over any
commutative ring so rational certificate evaluation uses the same formula. -/
def cayleyNumeratorMatrix {R : Type} [CommRing R]
    (x y z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1 + x * x - y * y - z * z,
      2 * (x * y - z),
      2 * (x * z + y);
     2 * (x * y + z),
      1 - x * x + y * y - z * z,
      2 * (y * z - x);
     2 * (x * z - y),
      2 * (y * z + x),
      1 - x * x - y * y + z * z]

/-- The rational rotation matrix with Cayley vector `(x, y, z)`. -/
noncomputable def cayleyMatrix (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let d := cayleyDenom x y z
  !![(1 + x ^ 2 - y ^ 2 - z ^ 2) / d,
      2 * (x * y - z) / d,
      2 * (x * z + y) / d;
     2 * (x * y + z) / d,
      (1 - x ^ 2 + y ^ 2 - z ^ 2) / d,
      2 * (y * z - x) / d;
     2 * (x * z - y) / d,
     2 * (y * z + x) / d,
      (1 - x ^ 2 - y ^ 2 + z ^ 2) / d]

theorem cayleyMatrix_eq_div_numerator (x y z : ℝ) :
    cayleyMatrix x y z = Matrix.of fun i j =>
      cayleyNumeratorMatrix x y z i j / cayleyDenom x y z := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyMatrix, cayleyNumeratorMatrix, pow_two]

theorem cayleyNumeratorMatrix_eq_denom_smul (x y z : ℝ) :
    cayleyNumeratorMatrix x y z =
      cayleyDenom x y z • cayleyMatrix x y z := by
  rw [cayleyMatrix_eq_div_numerator]
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  field_simp [cayleyDenom_ne]

/-- Cayley matrices are orientation-preserving orthogonal matrices. -/
theorem cayleyMatrix_mem_SO3 (x y z : ℝ) :
    cayleyMatrix x y z ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff,
    Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cayleyMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp [cayleyDenom_ne] <;>
      simp only [cayleyDenom] <;> ring
  · simp [cayleyMatrix, Matrix.det_fin_three]
    field_simp [cayleyDenom_ne]
    simp only [cayleyDenom]
    ring

/-- Trace is a rational function of the squared Cayley radius. -/
theorem trace_cayleyMatrix (x y z : ℝ) :
    Matrix.trace (cayleyMatrix x y z) =
      (3 - (x ^ 2 + y ^ 2 + z ^ 2)) / cayleyDenom x y z := by
  simp [Matrix.trace, cayleyMatrix, Fin.sum_univ_three]
  field_simp [cayleyDenom_ne]
  ring

/-- Every special orthogonal matrix of nonnegative trace has a Cayley vector
of squared radius at most three, giving a closed, bounded Cayley chart for the
nonnegative-trace rotations.

The Cayley vector is the skew part of `A` divided by `1 + tr A` (the vector part of the
quaternion of `A` over its scalar part). That `A` is the Cayley rotation of this vector is a
polynomial identity modulo the relations `A Aᵀ = 1`, `Aᵀ A = 1` and `adj A = Aᵀ`. -/
theorem exists_cayleyMatrix_of_trace_nonneg
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (htrace : 0 ≤ Matrix.trace A) :
    ∃ x y z : ℝ,
      x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 ∧ A = cayleyMatrix x y z := by
  obtain ⟨hO, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hA
  have hrow := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hO
  have hcol := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO
  -- a rotation is its own cofactor matrix
  have hcof : A.adjugate = Aᵀ := by
    have h := congrArg (Aᵀ * ·) (Matrix.mul_adjugate A)
    simpa [← Matrix.mul_assoc, hcol, hdet] using h
  simp only [← Matrix.ext_iff, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Fin.isValue,
    Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true, Matrix.one_apply_eq,
    Nat.reduceAdd, ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceEq, Fin.succ_ne_zero,
    Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    Matrix.cons_val_succ] at hrow hcol hcof
  obtain ⟨⟨R00, R01, R02⟩, ⟨-, R11, R12⟩, -, -, R22⟩ := hrow
  obtain ⟨⟨C00, C01, C02⟩, ⟨-, C11, C12⟩, -, -, C22⟩ := hcol
  obtain ⟨⟨K00, K10, K20⟩, ⟨K01, K11, K21⟩, K02, K12, K22⟩ := hcof
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three] at htrace
  -- the quaternion `(d, sx, sy, sz) / 2`, up to normalization
  set d := 1 + (A 0 0 + A 1 1 + A 2 2) with hd
  set sx := A 2 1 - A 1 2 with hsx
  set sy := A 0 2 - A 2 0 with hsy
  set sz := A 1 0 - A 0 1 with hsz
  have hdpos : 0 < d := by linarith
  have hx2 : (sx / d) ^ 2 = (1 + A 0 0 - A 1 1 - A 2 2) / d := by
    field_simp; linear_combination R11 + R22 - C00 + 2 * K00
  have hy2 : (sy / d) ^ 2 = (1 - A 0 0 + A 1 1 - A 2 2) / d := by
    field_simp; linear_combination R00 + R22 - C11 + 2 * K11
  have hz2 : (sz / d) ^ 2 = (1 - A 0 0 - A 1 1 + A 2 2) / d := by
    field_simp; linear_combination R00 + R11 - C22 + 2 * K22
  have hxy : sx / d * (sy / d) = (A 0 1 + A 1 0) / d := by
    field_simp; linear_combination K10 + K01 - R01 - C01
  have hxz : sx / d * (sz / d) = (A 0 2 + A 2 0) / d := by
    field_simp; linear_combination K20 + K02 - R02 - C02
  have hyz : sy / d * (sz / d) = (A 1 2 + A 2 1) / d := by
    field_simp; linear_combination K12 + K21 - R12 - C12
  refine ⟨sx / d, sy / d, sz / d, ?_, ?_⟩
  · rw [hx2, hy2, hz2, ← add_div, ← add_div, div_le_iff₀ hdpos]
    linarith
  · have hD : cayleyDenom (sx / d) (sy / d) (sz / d) = 4 / d := by
      rw [cayleyDenom, hx2, hy2, hz2]; field_simp; ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cayleyMatrix, hx2, hy2,
        hz2, hD, hxy, hxz, hyz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      field_simp <;> ring
end Cayley

end
