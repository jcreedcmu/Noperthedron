import Noperthedron.RationalApprox.RationalLocal
import Noperthedron.RationalApprox.EpsKapSpanning
import Noperthedron.RationalApprox.BoundsKappa3

/-!
# Bridge lemmas: approximate triangles → real triangles

These lemmas show that Aεℚ and κSpanning on a κ-approximate triangle P'
imply the corresponding real conditions (Aε and Spanning) on the exact triangle P.

The key ingredient is `bounds_kappa3_X` which bounds the inner product error
between `vecX`/`vecXℚ` applied to real/approximate vertices.
-/

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox

/-- Aεℚ on an approximate triangle implies Aε on the real triangle.
Uses `bounds_kappa3_X` to bound the inner product error by 3κ,
which is exactly absorbed by the 3κ slack in Aεℚ. -/
theorem aε_from_aeq
    (θ φ ε : ℝ) (hθ : θ ∈ Set.Icc (-4 : ℝ) 4) (hφ : φ ∈ Set.Icc (-4 : ℝ) 4)
    (P P' : Triangle)
    (hP : ∀ i : Fin 3, ‖P i‖ ≤ 1)
    (hk : ∀ i : Fin 3, ‖P i - P' i‖ ≤ κ)
    (hA : P'.Aεℚ (vecXℚ θ φ) ε) :
    P.Aε (vecX θ φ) ε := by
  rcases hA with ⟨σ, hσ, h⟩
  refine ⟨σ, hσ, ?_⟩
  intro i
  have hX : ‖⟪vecX θ φ, P i⟫ - ⟪vecXℚ θ φ, P' i⟫‖ ≤ 3 * κ := by
    simpa [vecX, vecXℚ] using
      (bounds_kappa3_X (θ := ⟨θ, hθ⟩) (φ := ⟨φ, hφ⟩) (P := P i) (P_ := P' i)
        (hP i) (hk i))
  have hσ2i : (-1 : ℝ) ^ σ * ⟪vecXℚ θ φ, P' i⟫ > √2 * ε + 3 * κ := h i
  have habs : |(-1 : ℝ) ^ σ| = 1 := abs_neg_one_zpow σ
  have hdiff : |(-1 : ℝ) ^ σ * (⟪vecX θ φ, P i⟫ - ⟪vecXℚ θ φ, P' i⟫)| ≤ 3 * κ := by
    rw [abs_mul, habs, one_mul]
    exact hX
  rw [abs_le] at hdiff
  have hmul : (-1 : ℝ)^σ * (⟪vecX θ φ, P i⟫ - ⟪vecXℚ θ φ, P' i⟫) ≤ 3 * κ := by
    linarith [hdiff.1, hdiff.2]
  change (-1 : ℝ)^σ * ⟪vecX θ φ, P i⟫ > √2 * ε
  linarith [hσ2i, hmul]

/-- κSpanning on an approximate triangle implies Spanning on the real triangle.
Direct application of `ek_spanning_imp_e_spanning` (Lemma 46). -/
theorem span_from_approx
    (P P' : Triangle) (ε θ φ : ℝ)
    (hθ : θ ∈ Set.Icc (-4 : ℝ) 4) (hφ : φ ∈ Set.Icc (-4 : ℝ) 4)
    (hk : κApproxTri P P') (hP : ∀ i : Fin 3, ‖P i‖ ≤ 1)
    (hspan : P'.κSpanning θ φ ε) :
    P.Spanning θ φ ε :=
  ek_spanning_imp_e_spanning P P' hk hP hθ hφ hspan

end Solution
