import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Bounding
import Noperthedron.Local.Prelims
import Noperthedron.Local.OriginInTriangle
import Noperthedron.Local.Spanp

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

def Triangle : Type := Fin 3 → ℝ³

/-- The triangle P is congruent to Q in the usual geometric sense -/
def Triangle.Congruent (P Q : Triangle) : Prop := by
  sorry

/-- [SY25] Definition 27. Note that the "+ 1" at the type Fin 3 wraps. -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℝ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) < ⟪rotR (π / 2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫

lemma triangle_ineq_aux
    {d x y : ℝ} (hd : 0 < d) (hy : d < y) (hx : |x - y| ≤ d) : 0 < x := by
  grind

/-- [SY25] Lemma 28 -/
theorem vecX_spanning {ε θ θ_ φ φ_ : ℝ} (P : Triangle)
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hSpanning: P.Spanning θ_ φ_ ε)
    (hP : ∀ i, ‖P i‖ ≤ 1)
    (hX : ∀ i, 0 < ⟪vecX θ φ, P i⟫) :
    vecX θ φ ∈ Spanp P := by
  obtain ⟨hε, hlt⟩ := hSpanning
  have h₁ : ∀ i, 0 < ⟪rotR (π/2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫ := by
    intro i
    -- lemma 24 -> Local.abs_sub_inner_bars_le
    have h₂ :=
      Local.abs_sub_inner_bars_le
        (rotR (π/2) ∘L rotM θ φ) (rotM θ φ)
        (rotR (π/2) ∘L rotM θ_ φ_) (rotM θ_ φ_)
        (P i) (P (i + 1))

    specialize hlt i

    rw [←ContinuousLinearMap.comp_sub] at h₂
    grw [hP, hP] at h₂
    grw [ContinuousLinearMap.opNorm_comp_le (rotR (π / 2)) (rotM θ_ φ_)] at h₂
    grw [ContinuousLinearMap.opNorm_comp_le] at h₂
    simp only [Bounding.rotR_norm_one, Bounding.rotM_norm_one, mul_one, one_mul] at h₂

    -- lemma 13 -> Bounding.norm_M_sub_lt
    have h₃ := Bounding.norm_M_sub_lt hε hθ hφ
    grw [h₃] at h₂
    have h₄ : √2 * ε + √2 * ε + √2 * ε * (√2 * ε) = 2 * ε * (√2 + ε) := by
      rw [show √2 * ε * (√2 * ε) = √2^2 * ε^2 by ring]
      simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
      ring
    rw [h₄] at h₂
    clear h₃ h₄
    have hd : 0 < 2 * ε * (√2 + ε) := by positivity
    exact triangle_ineq_aux hd hlt h₂

  -- apply lemma 26
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := Local.origin_in_triangle (h₁ 0) (h₁ 1) (h₁ 2)
  let S := a • (P 0) + b • (P 1) + c • (P 2)
  -- both S and vecX θ φ are in the kernel of rotM θ φ
  -- therefore S = λ * vecX θ φ for some λ.
  have h₂ : ∃ lam : ℝ, S = lam • vecX θ φ := by
    sorry
  obtain ⟨lam, hlam⟩ := h₂
  have h₄ : 0 < lam := by
    have h₃ : lam = ⟪vecX θ φ, lam • vecX θ φ⟫ := by
      rw [real_inner_smul_self_right]
      simp [vecX_norm_one]
    rw [← hlam] at h₃
    unfold S at h₃
    simp only [inner_add_right, real_inner_smul_right] at h₃
    rw [h₃]
    have hX0 := hX 0
    have hX1 := hX 1
    have hX2 := hX 2
    nlinarith only [ha, hb, hc, hX0, hX1, hX2]
  have h₅ : vecX θ φ = lam⁻¹ • S := by
    rw [hlam]
    rw [smul_smul]
    field_simp
    simp
  simp only [Spanp, Set.mem_setOf_eq]
  use fun i ↦ match i with
              | 0 => lam⁻¹ * a
              | 1 => lam⁻¹ * b
              | 2 => lam⁻¹ * c
  constructor
  · intro i
    fin_cases i <;> simp <;> positivity
  · simp [Fin.sum_univ_three, h₅, S, smul_smul]
