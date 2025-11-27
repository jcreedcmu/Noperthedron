import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.NormNum.NatFactorial
import Noperthedron.Lemma39
import Noperthedron.Basic

namespace RationalApprox

open scoped Nat -- for ! notation

noncomputable section

/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯$ up to and including the degree $2n-1$ term.
-/
def sin_psum (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯$ up to and including the degree $2n-2$ degree term.
-/
def cos_psum (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / (2 * i)!)

/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯ + x^{25}/25!$
-/
def sinℚ := sin_psum 13

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯ + x^{24}/24!$
-/
def cosℚ := cos_psum 13

/--
Frequently used constant for controlling the degree of approximation
of rational versions to real counterparts.
-/
def κ : ℝ := 1 / 10^10

end

theorem sin_psum_approx (x : ℚ) (n : ℕ) : |Real.sin x - sin_psum n x| ≤ |x|^(2 * n + 1) / (2 * n + 1)! := by
  sorry

theorem cos_psum_approx (x : ℚ) (n : ℕ) : |Real.cos x - cos_psum n x| ≤ |x|^(2 * n) / (2 * n)! := by
  sorry

theorem sinℚ_approx (x : ℚ) : |Real.sin x - sinℚ x| ≤ |x|^27 / 27! :=
  sin_psum_approx x 13

theorem cosℚ_approx (x : ℚ) : |Real.cos x - cosℚ x| ≤ |x|^26 / 26! :=
  cos_psum_approx x 13

theorem sinℚ_approx' (x : ℚ) (hx : x ∈ Set.Icc (-4) 4) : |Real.sin x - sinℚ x| ≤ κ / 7 := by
  have hx' : |x| ≤ 4 := abs_le.mpr hx
  have z := sinℚ_approx x
  grw [hx'] at z
  have : 4 ^ 27 / ↑27! ≤ κ / 7 := by
    norm_num [κ]
  grw [← this]
  exact z

theorem cosℚ_approx' (x : ℚ) (hx : x ∈ Set.Icc (-4) 4) : |Real.cos x - cosℚ x| ≤ κ / 7 := by
  have hx' : |x| ≤ 4 := abs_le.mpr hx
  have z := cosℚ_approx x
  grw [hx'] at z
  have : 4 ^ 26 / ↑26! ≤ κ / 7 := by
    norm_num [κ]
  grw [← this]
  exact z

inductive ApproximableEntry : Type where
  | zero : ApproximableEntry
  | one : ApproximableEntry
  | minus_one : ApproximableEntry
  | sin : ApproximableEntry
  | cos : ApproximableEntry
  | msin : ApproximableEntry
  | mcos : ApproximableEntry

def DistLtKappaEntry := ApproximableEntry × ApproximableEntry

noncomputable
def ApproximableEntry.actual (z : ℚ) : ApproximableEntry → ℝ
| .zero => 0
| .one => 1
| .minus_one => -1
| .sin => Real.sin z
| .cos => Real.cos z
| .msin => -Real.sin z
| .mcos => -Real.cos z

noncomputable
def DistLtKappaEntry.actual (dlke : DistLtKappaEntry) (x y : ℚ) :=
  dlke.fst.actual x * dlke.snd.actual y

noncomputable
def ApproximableEntry.approx (z : ℚ) : ApproximableEntry → ℝ
| .zero => 0
| .one => 1
| .minus_one => -1
| .sin => sinℚ z
| .cos => cosℚ z
| .msin => -sinℚ z
| .mcos => -cosℚ z

noncomputable
def DistLtKappaEntry.approx (dlke : DistLtKappaEntry) (x y : ℚ) :=
  dlke.fst.approx x * dlke.snd.approx y

noncomputable
def matrixActual {m n : ℕ} (A : Matrix (Fin m) (Fin n) DistLtKappaEntry) (x y : ℚ) : E n →L[ℝ] E m :=
   A.map (·.actual x y) |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def matrixApprox {m n : ℕ} (A : Matrix (Fin m) (Fin n) DistLtKappaEntry) (x y : ℚ) : E n →L[ℝ] E m :=
   A.map (·.approx x y) |>.toEuclideanLin.toContinuousLinearMap

theorem norm_matrix_actual_approx_le_kappa {m n : Finset.Icc 1 3} (A : Matrix (Fin m) (Fin n) DistLtKappaEntry) (x y : Set.Icc (-4) 4) :
    ‖matrixActual A x y - matrixApprox A x y‖ ≤ κ := by
  sorry
