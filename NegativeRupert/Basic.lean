import NegativeRupert.Rupert.Basic

open scoped Matrix

/--
A finite collection of vertices in ℝ³
-/
structure Shape : Type where
  size : ℕ
  vertices : Fin size → ℝ³

namespace Shape

def hull (s : Shape) : Set ℝ³ := convexHull ℝ (Set.range s.vertices)

end Shape

/- FIXME: Is there not a better way to name the standard euclidean basis?
This seems pretty verbose. -/
noncomputable
def e3 : Module.Basis (Fin 3) ℝ ℝ³ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

noncomputable
def e2 : Module.Basis (Fin 2) ℝ ℝ² := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

open Real

-- rotation about x-axis by θ
noncomputable
def Rx (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,     0,      0;
     0, cos θ, -sin θ;
     0, sin θ,  cos θ]

noncomputable
def Rx_linear (θ : ℝ) : ℝ³ →ₗ[ℝ] ℝ³ := (Rx θ).toLin e3 e3

noncomputable
def Rx_affine (θ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ := (Rx_linear θ).toAffineMap

-- rotation about y-axis by θ
noncomputable
def Ry (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, 0, -sin θ;
     0,     1,      0;
     sin θ, 0,  cos θ]

noncomputable
def Ry_linear (θ : ℝ) : ℝ³ →ₗ[ℝ] ℝ³ := (Ry θ).toLin e3 e3

noncomputable
def Ry_affine (θ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ := (Ry_linear θ).toAffineMap

-- rotation about z-axis by θ
noncomputable
def Rz (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0;
     sin θ,  cos θ, 0;
     0,      0,     1]

noncomputable
def Rz_linear (θ : ℝ) : ℝ³ →ₗ[ℝ] ℝ³ := (Rz θ).toLin e3 e3

noncomputable
def Rz_affine (θ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ := (Rz_linear θ).toAffineMap

-- [SY25] § 1.1 Definition 2
noncomputable
def rotR (α : ℝ) : ℝ² →ᵃ[ℝ] ℝ² :=
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![cos α, -sin α; sin α, cos α]
  (A.toLin e2 e2).toAffineMap

-- Derivative of rotR with respect to its parameter
noncomputable
def rotR' (α : ℝ) : ℝ² →ᵃ[ℝ] ℝ² :=
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![-sin α, -cos α; cos α, -sin α]
  (A.toLin e2 e2).toAffineMap

-- [SY25] § 1.1 Definition 2
noncomputable
def rotM (θ : ℝ) (φ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ² :=
  let A : Matrix (Fin 2) (Fin 3) ℝ :=
    !![-sin θ, cos θ, 0; -cos θ * cos φ, -sin θ * cos φ, sin φ]
  (A.toLin e3 e2).toAffineMap

-- Partial derivative of rotM with respect to θ
noncomputable
def rotMθ (θ : ℝ) (φ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ² :=
  let A : Matrix (Fin 2) (Fin 3) ℝ :=
    !![-cos θ, -sin θ, 0; sin θ * cos φ, -cos θ * cos φ, 0]
  (A.toLin e3 e2).toAffineMap

-- Partial derivative of rotM with respect to φ
noncomputable
def rotMφ (θ : ℝ) (φ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ² :=
  let A : Matrix (Fin 2) (Fin 3) ℝ :=
    !![0, 0, 0; cos θ * sin φ, sin θ * sin φ, cos φ]
  (A.toLin e3 e2).toAffineMap

theorem sin_neg_pi_div_two : Real.sin (-(π / 2)) = -1 := by
  simp only [Real.sin_neg, Real.sin_pi_div_two]

theorem cos_neg_pi_div_two : Real.cos (-(π / 2)) = 0 := by
  simp only [Real.cos_neg, Real.cos_pi_div_two]

infixr:80 " ∘ᵃ " => AffineMap.comp

-- This is R(α) M(θ, φ) in (5) in [SY25] § 2.2,
-- except we don't project to ℝ²
noncomputable
def rotRM (θ : ℝ) (φ : ℝ) (α : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ :=
  Rz_affine (-(π / 2)) ∘ᵃ Rz_affine α ∘ᵃ Ry_affine φ ∘ᵃ Rz_affine (-θ)

-- This is R(α) M(θ, φ) in (5) in [SY25] § 2.2,
noncomputable
def rotprojRM (θ : ℝ) (φ : ℝ) (α : ℝ) : ℝ³ →ᵃ[ℝ] ℝ² :=
  rotR α ∘ᵃ rotM θ φ
