import Noperthedron.RationalApprox.RationalLocal

/-!
# Bridge: approximate Aεℚ check → exact Aεℚ on real triangle

The soundness fields in Oracle.lean require `(Row.PTriangle row).Aεℚ vecX₁ℚ ε`
on the REAL triangle (transcendental coordinates). We cannot change Oracle.lean
(upstream of WitnessData cache).

Solution: prove Aεℚ on the real triangle from a stricter check on an approximate
triangle. The inner product error |⟪X, P_i⟫ - ⟪X, P'_i⟫| ≤ ‖X‖·‖P_i - P'_i‖
is bounded by (1+κ)·κ when ‖X‖ ≤ 1+κ and ‖P_i - P'_i‖ ≤ κ.

If the approximate inner product exceeds `√2·ε + 3κ + (1+κ)·κ`,
the real inner product exceeds `√2·ε + 3κ` (= Aεℚ threshold).
-/

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox

/-- If inner products with an approximate triangle exceed a stricter threshold,
    then Aεℚ holds on the real triangle.

    The extra margin `(1+κ)·κ` absorbs the inner product error from using
    approximate vertex coordinates instead of exact ones. -/
theorem aeq_real_of_aeq_approx_strict
    (P P' : Triangle) (X : ℝ³) (ε : ℝ)
    (hk : ∀ i : Fin 3, ‖P i - P' i‖ ≤ κ)
    (hX : ‖X‖ ≤ 1 + κ)
    (hA : ∃ σ ∈ ({-1, 1} : Set ℤ), ∀ i : Fin 3,
      (-1)^σ * ⟪X, P' i⟫ > √2 * ε + 3 * κ + (1 + κ) * κ) :
    P.Aεℚ X ε := by
  rcases hA with ⟨σ, hσ, h⟩
  refine ⟨σ, hσ, ?_⟩
  intro i
  have hκ : (0 : ℝ) ≤ κ := by norm_num [κ]
  have hdiff : |⟪X, P i⟫ - ⟪X, P' i⟫| ≤ (1 + κ) * κ := by
    calc |⟪X, P i⟫ - ⟪X, P' i⟫|
        = |⟪X, P i - P' i⟫| := by rw [inner_sub_right]
      _ ≤ ‖X‖ * ‖P i - P' i‖ := abs_real_inner_le_norm X (P i - P' i)
      _ ≤ (1 + κ) * κ := mul_le_mul hX (hk i) (norm_nonneg _) (by linarith)
  have habs : |(-1 : ℝ) ^ σ| = 1 := abs_neg_one_zpow σ
  have hsdiff : |(-1 : ℝ) ^ σ * (⟪X, P i⟫ - ⟪X, P' i⟫)| ≤ (1 + κ) * κ := by
    rw [abs_mul, habs, one_mul]; exact hdiff
  have hle : (-1 : ℝ) ^ σ * (⟪X, P i⟫ - ⟪X, P' i⟫) ≥ -((1 + κ) * κ) := by
    linarith [(abs_le.mp hsdiff).1]
  calc (-1 : ℝ) ^ σ * ⟪X, P i⟫
      = (-1) ^ σ * ⟪X, P' i⟫ + (-1) ^ σ * (⟪X, P i⟫ - ⟪X, P' i⟫) := by ring
    _ > (√2 * ε + 3 * κ + (1 + κ) * κ) + (-((1 + κ) * κ)) := by linarith [h i]
    _ = √2 * ε + 3 * κ := by ring

end Solution
