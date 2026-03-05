import Noperthedron.SolutionTable.ApproxVertices
import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.CheckAeComputable

/-!
# Per-row computable soundness checks

Combines approximate vertices with the squaring-trick Bool checks
to produce per-row verification functions suitable for native_decide.

These work entirely over ℚ, using the Row's integer fields directly.
-/

namespace Solution

open RationalApprox

/-! ### Rational row data extraction -/

/-- The common denominator for pose intervals. -/
def DENOM_Q : ℚ := 15360000

/-- Rational interval midpoint (matches Row.intervalMid cast to ℝ). -/
def intervalMidQ (row : Row) (p : Param) : ℚ :=
  ((row.interval.min p : ℚ) + row.interval.max p) / (2 * DENOM_Q)

/-- Rational interval half-width. -/
def intervalHalfWidthQ (row : Row) (p : Param) : ℚ :=
  ((row.interval.max p : ℚ) - row.interval.min p) / (2 * DENOM_Q)

/-- Rational localEps: max half-width over all 5 parameters. -/
def localEpsQ (row : Row) : ℚ :=
  let ws := [intervalHalfWidthQ row .θ₁, intervalHalfWidthQ row .φ₁,
             intervalHalfWidthQ row .θ₂, intervalHalfWidthQ row .φ₂,
             intervalHalfWidthQ row .α]
  ws.foldl max 0

/-- Rational pose angles. -/
def θ₁Q (row : Row) : ℚ := intervalMidQ row .θ₁
def φ₁Q (row : Row) : ℚ := intervalMidQ row .φ₁
def θ₂Q (row : Row) : ℚ := intervalMidQ row .θ₂
def φ₂Q (row : Row) : ℚ := intervalMidQ row .φ₂

/-! ### Per-row approximate triangle lookup -/

/-- Approximate P-triangle vertices for a row (rational). -/
def approxPTriQ (row : Row) : Fin 3 → (Fin 3 → ℚ) :=
  fun
  | 0 => approxVertexByIndex row.P1_index
  | 1 => approxVertexByIndex row.P2_index
  | 2 => approxVertexByIndex row.P3_index

/-- Approximate Q-triangle vertices for a row (rational). -/
def approxQTriQ (row : Row) : Fin 3 → (Fin 3 → ℚ) :=
  fun
  | 0 => approxVertexByIndex row.Q1_index
  | 1 => approxVertexByIndex row.Q2_index
  | 2 => approxVertexByIndex row.Q3_index

/-! ### Per-row Bool checks -/

/-- Check ae1 (Aεℚ on P-triangle with vecX₁ℚ) for a local leaf row. -/
def checkAe1Row (row : Row) : Bool :=
  let X := vecXQ (θ₁Q row) (φ₁Q row)
  let P := approxPTriQ row
  let ε := localEpsQ row
  checkAeTriSq P X ε

/-- Check ae2 (Aεℚ on Q-triangle with vecX₂ℚ) for a local leaf row. -/
def checkAe2Row (row : Row) : Bool :=
  let X := vecXQ (θ₂Q row) (φ₂Q row)
  let Q := approxQTriQ row
  let ε := localEpsQ row
  checkAeTriSq Q X ε

/-- Check span1 (κSpanning on P-triangle) for a local leaf row. -/
def checkSpan1Row (row : Row) : Bool :=
  let P := approxPTriQ row
  let ε := localEpsQ row
  checkSpanTriSq (θ₁Q row) (φ₁Q row) P ε

/-- Check span2 (κSpanning on Q-triangle) for a local leaf row. -/
def checkSpan2Row (row : Row) : Bool :=
  let Q := approxQTriQ row
  let ε := localEpsQ row
  checkSpanTriSq (θ₂Q row) (φ₂Q row) Q ε

/-- Combined check for all 4 Step-3 soundness fields on a local leaf row. -/
def checkStep3Row (row : Row) : Bool :=
  row.nodeType != 2 ||
    (checkAe1Row row && checkAe2Row row && checkSpan1Row row && checkSpan2Row row)

end Solution
