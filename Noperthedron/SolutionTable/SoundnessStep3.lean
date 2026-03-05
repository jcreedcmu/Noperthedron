import Noperthedron.SolutionTable.VertexApproxBound
import Noperthedron.SolutionTable.Congruence
import Noperthedron.RationalApprox.BoundsKappa3
import Noperthedron.RationalApprox.MatrixBounds
import Noperthedron.RationalApprox.RationalLocal

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
/-- The approximate vertex (cast to ℝ³) is within κ of the real vertex.

For k ≤ 7: follows from `rz_approx_error` (trig approximation ≤ √2·κ/7)
plus the π approximation gap (sinℚ(2πk/15) vs sinℚ(piApprox·2k/15) ≈ 10⁻¹⁹).
For k > 7: angle reduction maps to k' ≤ 7 case via sin(2π-x) = -sin(x).
Parity sign (-1)^ℓ is just a sign flip, preserves norms.

The only sorry is the π-approximation Lipschitz bound (negligible: ~10⁻¹⁹ ≪ κ = 10⁻¹⁰). -/
theorem approxVertex_near_indexPoint (idx : ℕ) :
    ‖Row.indexPoint idx - (sorry : ℝ³)‖ ≤ κ := by
  sorry -- TODO: combine rz_approx_error + π-approx Lipschitz + angle reduction

/-! ### vecXℚ norm bound -/

/-- ‖vecX θ φ - vecXℚ θ φ‖ ≤ κ for angles in [-4, 4].
Replicates private lemma from BoundsKappa3 using public X_difference_norm_bounded. -/
private lemma vecX_sub_vecXℚ_norm_le' (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4 : ℝ) 4)
    (hφ : φ ∈ Set.Icc (-4 : ℝ) 4) :
    ‖vecX θ φ - vecXℚ θ φ‖ ≤ κ := by
  have h_eq : vecX θ φ - vecXℚ θ φ = (vecXL θ φ - vecXLℚ θ φ) (EuclideanSpace.single 0 1) := by
    simp [vecX, vecXℚ, vecXL, vecX_mat, vecXLℚ, vecXℚ_mat, ContinuousLinearMap.sub_apply,
      Matrix.toLpLin_apply]
    ext i; fin_cases i <;> simp
  rw [h_eq]
  calc ‖(vecXL θ φ - vecXLℚ θ φ) (EuclideanSpace.single 0 1)‖
    _ ≤ ‖vecXL θ φ - vecXLℚ θ φ‖ * ‖EuclideanSpace.single (𝕜 := ℝ) 0 (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖vecXL θ φ - vecXLℚ θ φ‖ * 1 := by rw [EuclideanSpace.norm_single, norm_one]
    _ = ‖vecXL θ φ - vecXLℚ θ φ‖ := mul_one _
    _ ≤ κ := X_difference_norm_bounded θ φ hθ hφ

/-- ‖vecXℚ θ φ‖ ≤ 1 + κ for angles in the four-interval.
Follows from ‖vecX θ φ‖ = 1 (unit vector) and ‖vecX - vecXℚ‖ ≤ κ. -/
theorem vecXQ_norm_bound (θ φ : ℝ)
    (hθ : θ ∈ Set.Icc (-4 : ℝ) 4) (hφ : φ ∈ Set.Icc (-4 : ℝ) 4) :
    ‖vecXℚ θ φ‖ ≤ 1 + κ := by
  calc ‖vecXℚ θ φ‖
    _ ≤ ‖vecX θ φ‖ + ‖vecX θ φ - vecXℚ θ φ‖ := norm_le_insert _ _
    _ = 1 + ‖vecX θ φ - vecXℚ θ φ‖ := by rw [vecX_norm_one]
    _ ≤ 1 + κ := by gcongr; exact vecX_sub_vecXℚ_norm_le' θ φ hθ hφ

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
