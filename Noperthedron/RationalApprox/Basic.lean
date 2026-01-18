import Noperthedron.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RationalApprox

notation "ℚ³" => EuclideanSpace ℚ (Fin 3)
notation "ℚ²" => EuclideanSpace ℚ (Fin 2)

instance : Coe ℚ² ℝ² where
  coe q := WithLp.toLp 2 (q ·)

instance : Coe ℚ³ ℝ³ where
  coe q := WithLp.toLp 2 (q ·)

def Triangle : Type := Fin 3 → ℚ³

noncomputable section

open scoped Nat -- for ! notation
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

def κApproxMat {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (A' : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ‖(A - A'.map (fun x => (↑x : ℝ))).toEuclideanLin.toContinuousLinearMap‖ ≤ κ

def κApproxPoint {m n : ℕ} (A A' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ‖(A - A').toEuclideanLin.toContinuousLinearMap‖ ≤ κ

end

noncomputable
def rotMℚ_mat (θ : ℚ) (φ : ℚ) : Matrix (Fin 2) (Fin 3) ℚ :=
  !![-sinℚ θ, cosℚ θ, 0; -cosℚ θ * cosℚ φ, -sinℚ θ * cosℚ φ, sinℚ φ]

/--
This is just a copy of Mathlib's `Matrix.toEuclideanLin2` which relaxes RCLike k to
Field k. Also I replaced the blackboard bold k with normal k because emacs lsp-mode
gets confused by unicode codepoints too large for single UTF16 encodings.
-/
def _root_.Matrix.toEuclideanLin2 {k m n : Type} [Field k] [Fintype n] [DecidableEq n] :
  Matrix m n k ≃ₗ[k] EuclideanSpace k n →ₗ[k] EuclideanSpace k m :=
  Matrix.toLin' ≪≫ₗ
    LinearEquiv.arrowCongr (WithLp.linearEquiv _ k (n → k)).symm
      (WithLp.linearEquiv _ k (m → k)).symm

/--
This is merely linear instead of continuous-linear because
.toContinuousLinearMap only works on Cauchy-complete spaces.
-/
noncomputable
def rotMℚ (θ φ : ℚ) : ℚ³ →ₗ[ℚ] ℚ² :=
  rotMℚ_mat θ φ |>.toEuclideanLin2
