import Mathlib.Data.Finset.Max

import Noperthedron.SolutionTable.Defs
import Noperthedron.Vertices.Python
import Noperthedron.Vertices.Trig

/-!
# Global Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational global theorem. Everything
here is computable — no `noncomputable` keyword.
-/

namespace Noperthedron.Solution

/-! ## Matrix-vector application

Computable versions of the 2×3 and 2×2 matrix-vector products from
`RationalApprox/Basic.lean`. Each function applies a specific rotation
matrix to a vector and returns the result.
-/

/-- M(θ,φ) · v — the projection matrix. -/
def applyM (θ φ : ℚ) (v : Fin 3 → ℚ) : Fin 2 → ℚ
  | 0 => -(sinQ θ) * v 0 + cosQ θ * v 1
  | 1 => -(cosQ θ) * cosQ φ * v 0 - sinQ θ * cosQ φ * v 1 + sinQ φ * v 2

/-- Mθ(θ,φ) · v — ∂M/∂θ applied to v. -/
def applyMθ (θ φ : ℚ) (v : Fin 3 → ℚ) : Fin 2 → ℚ
  | 0 => -(cosQ θ) * v 0 - sinQ θ * v 1
  | 1 => sinQ θ * cosQ φ * v 0 - cosQ θ * cosQ φ * v 1

/-- Mφ(θ,φ) · v — ∂M/∂φ applied to v. -/
def applyMφ (θ φ : ℚ) (v : Fin 3 → ℚ) : Fin 2 → ℚ
  | 0 => 0
  | 1 => cosQ θ * sinQ φ * v 0 + sinQ θ * sinQ φ * v 1 + cosQ φ * v 2

/-- R(α) · u — in-plane rotation. -/
def applyR (α : ℚ) (u : Fin 2 → ℚ) : Fin 2 → ℚ
  | 0 => cosQ α * u 0 - sinQ α * u 1
  | 1 => sinQ α * u 0 + cosQ α * u 1

/-- R'(α) · u — derivative of in-plane rotation. -/
def applyR' (α : ℚ) (u : Fin 2 → ℚ) : Fin 2 → ℚ
  | 0 => -(sinQ α) * u 0 - cosQ α * u 1
  | 1 => cosQ α * u 0 - sinQ α * u 1

/-! ## Gℚ and Hℚ computation

Direct rational computation matching the formulas in
`RationalApprox/RationalGlobal.lean`.
-/

/-- Rational G function: measures how far inner-shadow vertex S sticks out. -/
def computeGQ (θ₁ φ₁ α ε : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) : ℚ :=
  let m1S := applyM θ₁ φ₁ S
  let inner := (applyR α m1S) ⬝ᵥ w
  let t1 := |(applyR' α m1S) ⬝ᵥ w|
  let t2 := |(applyR α (applyMθ θ₁ φ₁ S)) ⬝ᵥ w|

  let t3 := |(applyR α (applyMφ θ₁ φ₁ S)) ⬝ᵥ w|
  inner - ε * (t1 + t2 + t3) - 9 * ε ^ 2 / 2 - 4 * κQ * (1 + 3 * ε)

/-- Rational H function: measures how far outer-shadow vertex P reaches. -/
def computeHQ (θ₂ φ₂ ε : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) : ℚ :=
  let m2P := applyM θ₂ φ₂ P
  let outer := m2P ⬝ᵥ w
  let t1 := |(applyMθ θ₂ φ₂ P) ⬝ᵥ w|
  let t2 := |(applyMφ θ₂ φ₂ P) ⬝ᵥ w|
  outer + ε * (t1 + t2) + 2 * ε ^ 2 + 3 * κQ * (1 + 2 * ε)

/-- Maximum H over all 90 vertices. -/
def computeMaxHQ (θ₂ φ₂ ε : ℚ) (w : Fin 2 → ℚ) : ℚ :=
  let values := (computeHQ θ₂ φ₂ ε w) ∘ pythonVertex
  let range := Finset.image values Finset.univ
  range.max' (by use values 0; simp_all [range])

abbrev _root_.Noperthedron.Solution.Row.G_gt_maxH (r : Row) : Prop :=
  computeGQ r.θ₁ r.φ₁ r.α r.epsilon r.S r.w > computeMaxHQ r.θ₂ r.φ₂ r.epsilon r.w

/-! ## The main checker -/

/-- Assertion that a row constitutes a valid application of the rational global theorem. -/
@[mk_iff]
structure Row.ValidGlobal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 1
  w_unit : row.wx_numerator ^ 2 + row.wy_numerator ^ 2 = (row.w_denominator : ℤ) ^ 2
  w_denominator_pos : 0 < row.w_denominator
  θ₁_lb : -4 ≤ row.θ₁
  θ₁_ub : row.θ₁ ≤ 4
  φ₁_lb : -4 ≤ row.φ₁
  φ₁_ub : row.φ₁ ≤ 4
  θ₂_lb : -4 ≤ row.θ₂
  θ₂_ub : row.θ₂ ≤ 4
  φ₂_lb : -4 ≤ row.φ₂
  φ₂_ub : row.φ₂ ≤ 4
  α_lb : -4 ≤ row.α
  α_ub : row.α ≤ 4
  epsilon_pos : 0 < row.epsilon
  G_gt_maxH : row.G_gt_maxH

instance (row : Row) : Decidable (Row.ValidGlobal row) :=
  decidable_of_iff _ (Row.validGlobal_iff row).symm

/-! ## Smoke test -/

/-- Row 91 from `data/solution_tree_300.csv` — the first global leaf. -/
def testGlobalRow : Row := {
  ID := 91, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := VertexIndex.ofFin90 ⟨39, by omega⟩,
  wx_numerator := 5319166373, wy_numerator := 15662395164,
  w_denominator := 16540984045,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testGlobalRow.ValidGlobal

