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
    Since `Aεℚ` uses `σ ∈ ({-1, 1} : Set ℤ)` and `(-1)^σ` where both values
    of σ give `(-1)^σ = -1`, the condition reduces to checking that all
    negated inner products exceed the threshold. We also check the positive
    sign (corresponding to `σ = 0` if the definition is later corrected). -/
def checkAeTriSq (verts : Fin 3 → (Fin 3 → ℚ)) (X : Fin 3 → ℚ) (ε : ℚ) : Bool :=
  let dots : Fin 3 → ℚ := fun i => dotQ X (verts i)
  -- Check negated dots (matches (-1)^σ = -1 for σ ∈ {-1, 1})
  (checkAeVertexSq (-(dots 0)) ε && checkAeVertexSq (-(dots 1)) ε && checkAeVertexSq (-(dots 2)) ε) ||
  -- Also check positive dots (for robustness / if σ set is corrected to {0, 1})
  (checkAeVertexSq (dots 0) ε && checkAeVertexSq (dots 1) ε && checkAeVertexSq (dots 2) ε)

/-! ### Computable κSpanning check -/

/-- Apply rotMℚ matrix to a ℚ³ vector, returning ℚ² result. -/
def rotMQ_apply (θ φ : ℚ) (P : Fin 3 → ℚ) : Fin 2 → ℚ :=
  fun
  | 0 => -(sinℚ θ) * P 0 + (cosℚ θ) * P 1
  | 1 => -(cosℚ θ) * (cosℚ φ) * P 0 - (sinℚ θ) * (cosℚ φ) * P 1 + (sinℚ φ) * P 2

/-- Apply 90° rotation in ℚ². -/
def rotR_pi2_apply (v : Fin 2 → ℚ) : Fin 2 → ℚ :=
  fun
  | 0 => -(v 1)
  | 1 => v 0

/-- Rational dot product of two ℚ² vectors. -/
def dotQ2 (a b : Fin 2 → ℚ) : ℚ := a 0 * b 0 + a 1 * b 1

/-- Compute the κSpanning inner product ⟪rotR(π/2)(rotMℚ θ φ P_i), rotMℚ θ φ P_{i+1}⟫
    as a rational number. -/
def spanInnerQ (θ φ : ℚ) (Pi Pj : Fin 3 → ℚ) : ℚ :=
  dotQ2 (rotR_pi2_apply (rotMQ_apply θ φ Pi)) (rotMQ_apply θ φ Pj)

/-- Check κSpanning inequality for a single pair via squaring trick.
    Checks: inner > 2ε(√2+ε) + 12κ (extra 6κ for vertex approximation margin).
    Rearranged: (inner - 2ε² - 12κ) > 0 ∧ (inner - 2ε² - 12κ)² > 8ε². -/
def checkSpanPairSq (inner : ℚ) (ε : ℚ) : Bool :=
  let κ : ℚ := 1 / 10^10
  let shifted := inner - 2 * ε ^ 2 - 12 * κ
  shifted > 0 && shifted ^ 2 > 8 * ε ^ 2

/-- Check κSpanning for a triangle given rational vertex coordinates.
    Checks all 3 pairs (i, i+1 mod 3). -/
def checkSpanTriSq (θ φ : ℚ) (verts : Fin 3 → (Fin 3 → ℚ)) (ε : ℚ) : Bool :=
  checkSpanPairSq (spanInnerQ θ φ (verts 0) (verts 1)) ε &&
  checkSpanPairSq (spanInnerQ θ φ (verts 1) (verts 2)) ε &&
  checkSpanPairSq (spanInnerQ θ φ (verts 2) (verts 0)) ε

end Solution
