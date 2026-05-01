import Noperthedron.Basic
import Noperthedron.Pose
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RationalApprox

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
def κℚ : ℚ := 1 / 10^10
def κ : ℝ := 1 / 10^10

def κApproxMat {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (A' : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ‖(A - A'.map (fun x => (↑x : ℝ))).toEuclideanLin.toContinuousLinearMap‖ ≤ κ

def κApproxPoint {m n : ℕ} (A A' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ‖(A - A').toEuclideanLin.toContinuousLinearMap‖ ≤ κ

/--
  A real polyhedron A and a rational polyhedron B that is a κ-approximation of A.
-/
structure κApproxPoly {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Polyhedron ι₁ ℝ³) (B : Polyhedron ι₂ (Fin 3 → ℚ)) where
  bijection : ι₁ ≃ ι₂
  approx : ∀ a : ι₁, ‖(A.v a : ℝ³) - toR3 (B.v (bijection a))‖ ≤ κ

end

def rotMℚ_mat {k : Type} [Field k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-sinℚ θ, cosℚ θ, 0; -cosℚ θ * cosℚ φ, -sinℚ θ * cosℚ φ, sinℚ φ]

def rotMθℚ_mat {k : Type} [Field k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-cosℚ θ, -sinℚ θ, 0; sinℚ θ * cosℚ φ, -cosℚ θ * cosℚ φ, 0]

def rotMφℚ_mat {k : Type} [Field k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ]

def rotRℚ_mat {k : Type} [Field k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![cosℚ α, -sinℚ α;
     sinℚ α,  cosℚ α]

def rotR'ℚ_mat {k : Type} [Field k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![-sinℚ α, -cosℚ α;
     cosℚ α,  -sinℚ α]

def vecXℚ_mat {k : Type} [Field k] (θ : k) (φ : k) : Matrix (Fin 3) (Fin 1) k :=
  !![ cosℚ θ * sinℚ φ; sinℚ θ * sinℚ φ; cosℚ φ ]

/-
These are merely linear instead of continuous-linear because
.toContinuousLinearMap only works on Cauchy-complete spaces.
-/

def rotMℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMℚ_mat θ φ |>.toLin'

def rotMθℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMθℚ_mat θ φ |>.toLin'

def rotMφℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMφℚ_mat θ φ |>.toLin'

def rotRℚ (α : ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotRℚ_mat α |>.toLin'

def rotR'ℚ (α : ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotR'ℚ_mat α |>.toLin'

def vecXLℚ (θ φ : ℚ) : (Fin 1 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) :=
  vecXℚ_mat θ φ |>.toLin'

def vecXℚ (θ : ℚ) (φ : ℚ) : (Fin 3 → ℚ) :=
  ![ cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ ]

def _root_.Pose.rotRℚ (p : Pose ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := _root_.RationalApprox.rotRℚ p.α

def _root_.Pose.rotR'ℚ (p : Pose ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := _root_.RationalApprox.rotR'ℚ p.α

def _root_.Pose.rotM₁ℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂ℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁θℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂θℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁φℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂φℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφℚ p.θ₂ p.φ₂

def _root_.Pose.innerℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := p.rotRℚ ∘ₗ p.rotM₁ℚ
def _root_.Pose.outerℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := p.rotM₂ℚ
def _root_.Pose.vecX₁ℚ (p : Pose ℚ) : (Fin 3 → ℚ) := vecXℚ (p.θ₁) (p.φ₁)
def _root_.Pose.vecX₂ℚ (p : Pose ℚ) : (Fin 3 → ℚ) := vecXℚ (p.θ₂) (p.φ₂)

noncomputable
def rotMℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMφℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotRℚℝ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotRℚ_mat α |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotR'ℚℝ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotR'ℚ_mat α |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def vecXLℚℝ (θ φ : ℝ) : Euc(1) →L[ℝ] ℝ³ :=
  vecXℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def vecXℚℝ (θ : ℝ) (φ : ℝ) : ℝ³ :=
  !₂[ cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ ]

noncomputable section
def _root_.Pose.rotRℚℝ (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.RationalApprox.rotRℚℝ p.α
def _root_.Pose.rotR'ℚℝ (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.RationalApprox.rotR'ℚℝ p.α
def _root_.Pose.rotM₁ℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMℚℝ p.θ₁ p.φ₁
def _root_.Pose.rotM₂ℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMℚℝ p.θ₂ p.φ₂
def _root_.Pose.rotM₁θℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMθℚℝ p.θ₁ p.φ₁
def _root_.Pose.rotM₂θℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMθℚℝ p.θ₂ p.φ₂
def _root_.Pose.rotM₁φℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMφℚℝ p.θ₁ p.φ₁
def _root_.Pose.rotM₂φℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMφℚℝ p.θ₂ p.φ₂
def _root_.Pose.innerℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := p.rotRℚℝ ∘L p.rotM₁ℚℝ
def _root_.Pose.outerℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := p.rotM₂
def _root_.Pose.vecX₁ℚℝ (p : Pose ℝ) : ℝ³ := vecXℚℝ (p.θ₁) (p.φ₁)
def _root_.Pose.vecX₂ℚℝ (p : Pose ℝ) : ℝ³ := vecXℚℝ (p.θ₂) (p.φ₂)
end

structure UpperSqrt where
  f : ℚ → ℚ
  bound : ∀ (x : ℚ), 0 ≤ x → √x ≤ f x

def UpperSqrt.norm {n : ℕ} (s : UpperSqrt) (v : Fin n → ℚ) : ℚ := s.f (v ⬝ᵥ v)

structure LowerSqrt where
  f : ℚ → ℚ
  bound : ∀ (x : ℚ), 0 ≤ x → f x ≤ √x

def LowerSqrt.norm {n : ℕ} (s : LowerSqrt) (v : Fin n → ℚ) : ℚ := s.f (v ⬝ᵥ v)

structure Approx where
  lower_sqrt : LowerSqrt
  upper_sqrt : UpperSqrt
  upper_sqrt_two : ℚ
  upper_sqrt_two_gt_sqrt_two : upper_sqrt_two > √2
  upper_sqrt_five : ℚ
  upper_sqrt_five_gt_sqrt_five : upper_sqrt_five > √5

def Approx.upper_norm {n : ℕ} (approx : Approx) (v : Fin n → ℚ) : ℚ :=
  approx.upper_sqrt.f (v ⬝ᵥ v)

def Approx.lower_norm {n : ℕ} (approx : Approx) (v : Fin n → ℚ) : ℚ :=
  approx.lower_sqrt.f (v ⬝ᵥ v)
