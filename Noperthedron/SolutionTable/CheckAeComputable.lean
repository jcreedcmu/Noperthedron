import Noperthedron.RationalApprox.Basic

/-!
# Computable Aεℚ check via squaring trick

Architecture:
1. Given a row, compute `vecXℚ` from rational pose angles (computable ℚ)
2. Given a rational approximate vertex `P'_i` (from lookup table)
3. Compute inner product `⟪vecXℚ, P'_i⟫` as a rational number
4. Apply squaring trick: check `|dot| - threshold > 0 ∧ (|dot| - threshold)² > 2ε²`
   where threshold = `3κ + (1+κ)κ` (stricter than Aεℚ's `3κ` to absorb approx error)
5. Bridge via `aeq_real_of_aeq_approx_strict`

For native_decide, step 2 requires a computable rational vertex table
(to be defined in a separate file with the 90 approximate nopert vertices).
-/

namespace Solution

open RationalApprox

/-! ### Computable rational arithmetic -/

/-- Rational dot product of two ℚ³ vectors. -/
def dotQ (a b : Fin 3 → ℚ) : ℚ :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- vecXℚ components as rational functions of rational angles.
    Matches `RationalApprox.vecXℚ` when cast to ℝ. -/
def vecXQ (θ φ : ℚ) : Fin 3 → ℚ :=
  fun
  | 0 => cosℚ θ * sinℚ φ
  | 1 => sinℚ θ * sinℚ φ
  | 2 => cosℚ φ

/-- The stricter threshold for Aεℚ on approximate triangles.
    Standard threshold is `3κ`, we add `(1+κ)κ` for approximation error. -/
def aeqStrictThreshold : ℚ :=
  3 * (1 / 10^10) + (1 + 1 / 10^10) * (1 / 10^10)

/-- Check if a single inner product exceeds the Aεℚ threshold via squaring.
    Returns true if `|dot| > √2 * ε + aeqStrictThreshold`. -/
def checkAeVertexSq (dot : ℚ) (ε : ℚ) : Bool :=
  let shifted := dot - aeqStrictThreshold
  shifted > 0 && shifted ^ 2 > 2 * ε ^ 2

/-- Check Aεℚ for a triangle given rational vertex coordinates and pose data.
    Tries both signs σ ∈ {-1, 1} and checks all 3 vertices. -/
def checkAeTriSq (verts : Fin 3 → (Fin 3 → ℚ)) (X : Fin 3 → ℚ) (ε : ℚ) : Bool :=
  let dots : Fin 3 → ℚ := fun i => dotQ X (verts i)
  -- Try σ = 0 (positive sign): all dots must pass
  (checkAeVertexSq (dots 0) ε && checkAeVertexSq (dots 1) ε && checkAeVertexSq (dots 2) ε) ||
  -- Try σ = 1 (negative sign): all negated dots must pass
  (checkAeVertexSq (-(dots 0)) ε && checkAeVertexSq (-(dots 1)) ε && checkAeVertexSq (-(dots 2)) ε)

end Solution
