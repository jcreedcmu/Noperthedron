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

/- The below definitions are [SY25] Definition 37 -/

open scoped Nat -- for ! notation
/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯$ up to and including the degree $2n-1$ term.
-/
def sin_psum {k : Type} [Field k] (n : ℕ) (x : k) : k :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯$ up to and including the degree $2n-2$ degree term.
-/
def cos_psum {k : Type} [Field k] (n : ℕ) (x : k) : k :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / (2 * i)!)

/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯ + x^{25}/25!$
-/
def sinℚ {k : Type} [Field k] := sin_psum (k := k) 13

lemma sinℚ_match (x : ℚ) : sinℚ (k := ℚ) x = sinℚ (k := ℝ) x := by
  unfold sinℚ sin_psum; push_cast; rfl

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯ + x^{24}/24!$
-/
def cosℚ {k : Type} [Field k] := cos_psum (k := k) 13

lemma cosℚ_match (x : ℚ) : cosℚ (k := ℚ) x = cosℚ (k := ℝ) x := by
  unfold cosℚ cos_psum; push_cast; rfl

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
def rotMℚ_mat {k : Type} [Field k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-sinℚ θ, cosℚ θ, 0; -cosℚ θ * cosℚ φ, -sinℚ θ * cosℚ φ, sinℚ φ]

noncomputable
def rotMθℚ_mat {k : Type} [Field k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-cosℚ θ, -sinℚ θ, 0; sinℚ θ * cosℚ φ, -cosℚ θ * cosℚ φ, 0]

noncomputable
def rotMφℚ_mat {k : Type} [Field k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ]

noncomputable
def rotRℚ_mat {k : Type} [Field k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![cosℚ α, -sinℚ α;
     sinℚ α,  cosℚ α]

noncomputable
def rotR'ℚ_mat {k : Type} [Field k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![-sinℚ α, -cosℚ α;
     cosℚ α,  -sinℚ α]

/--
These are merely linear instead of continuous-linear because
.toContinuousLinearMap only works on Cauchy-complete spaces.
-/
noncomputable
def rotMℚ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθℚ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMφℚ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotRℚ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotRℚ_mat α |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotR'ℚ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotR'ℚ_mat α |>.toEuclideanLin.toContinuousLinearMap
