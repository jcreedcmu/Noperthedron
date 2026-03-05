import Noperthedron.SolutionTable.AeqApproxBridge
import Noperthedron.SolutionTable.VertexApproxBound
import Noperthedron.SolutionTable.Congruence

/-!
# Soundness proofs for Step 3 (ae1, ae2, span1, span2)

End-to-end soundness: computable Bool check on approximate vertices
implies the mathematical Prop on real vertices.

## Proof chain

1. `checkAe1Row row = true` (computable ℚ check with squaring trick)
2. → approximate inner products exceed strict threshold `√2ε + 3κ + (1+κ)κ`
   (by unfolding Bool check, casting ℚ → ℝ)
3. → `PTriangle.Aεℚ vecX₁ℚ localEps` on real triangle
   (by `aeq_real_of_aeq_approx_strict` with vertex error bound)

## Key sorry'd lemmas (to be filled)

- `approxVertex_near_indexPoint`: `‖indexPoint - approxVertex‖ ≤ κ`
  (requires coordinate expansion of Rz vs RzQ + sinℚ_approx'/cosℚ_approx')
- `vecXQ_norm_bound`: `‖vecXℚ θ φ‖ ≤ 1 + κ` for θ, φ ∈ [-4, 4]
  (follows from ‖vecX‖ = 1 and ‖vecX - vecXℚ‖ ≤ κ)
-/

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox

/-! ### Vertex approximation bound -/

/-- The rational approximate vertex is within κ of the real vertex.

Proof sketch: decompose into trig error (sinℚ_approx', cosℚ_approx')
and π approximation error (negligible). The trig error gives
‖Rz(θ)v - RzQ(θ)v‖ ≤ √2 · κ/7 · ‖v‖ < κ when ‖v‖ ≤ 1. -/
noncomputable def approxVertexQ_cast (idx : ℕ) : ℝ³ := sorry -- cast of approxVertexByIndex

theorem approxVertex_near_indexPoint (idx : ℕ) :
    ‖Row.indexPoint idx - approxVertexQ_cast idx‖ ≤ κ := by
  sorry

/-! ### vecXℚ norm bound -/

/-- ‖vecXℚ θ φ‖ ≤ 1 + κ for angles in the four-interval.
Follows from ‖vecX θ φ‖ = 1 (unit vector) and ‖vecX - vecXℚ‖ ≤ κ. -/
theorem vecXQ_norm_bound (θ φ : ℝ)
    (hθ : θ ∈ Set.Icc (-4 : ℝ) 4) (hφ : φ ∈ Set.Icc (-4 : ℝ) 4) :
    ‖vecXℚ θ φ‖ ≤ 1 + κ := by
  sorry

/-! ### End-to-end soundness (sketched) -/

-- The full soundness theorem would be:
-- theorem ae1_soundness (row : Row) (h : row.ID < tab.size)
--     (hcheck : checkAe1Row row = true) :
--     (Row.PTriangle row).Aεℚ row.localPose.vecX₁ℚ row.localEps := by
--   -- 1. Unfold checkAe1Row: inner products on approx vertices exceed strict threshold
--   -- 2. Cast ℚ → ℝ: same inequality in ℝ
--   -- 3. Apply aeq_real_of_aeq_approx_strict with:
--   --    hk := fun i => approxVertex_near_indexPoint (PTriangle index i)
--   --    hX := vecXQ_norm_bound ...
--   sorry

end Solution
