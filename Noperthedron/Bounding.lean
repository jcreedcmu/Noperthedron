import Noperthedron.Basic
import Noperthedron.Bounding.Lemma11
import Noperthedron.Bounding.Lemma12
import Noperthedron.Bounding.OpNorm

open scoped RealInnerProductSpace Real

namespace Bounding

theorem norm_RxRy_minus_id_le {α β : ℝ} : ‖RxL α ∘L RyL β - 1‖ ≤ √(α ^ 2 + β ^ 2) := by
  have := lemma12 (α := α) (β := β) zero_ne_one
  simp only [rot3] at this
  exact this

theorem norm_M_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖rotM θ φ - rotM θ_ φ_‖ < √2 * ε := by
  by_cases h₁ : θ = θ_ ∧ φ = φ_
  · have h₂ : ‖rotM θ φ - rotM θ_ φ_‖ = 0 := by
      obtain ⟨hθ₁, hφ₁⟩ := h₁
      simp [hθ₁, hφ₁]
    rw [h₂]
    positivity
  simp only [rotM_identity, ←ContinuousLinearMap.comp_sub]
  grw [ContinuousLinearMap.opNorm_comp_le, reduceL_norm, one_mul]
  sorry

theorem norm_X_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖vecX θ φ - vecX θ_ φ_‖ < √2 * ε := by
  by_cases h₁ : θ = θ_ ∧ φ = φ_
  · have h₂ : ‖vecX θ φ - vecX θ_ φ_‖ = 0 := by
      obtain ⟨hθ₁, hφ₁⟩ := h₁
      simp [hθ₁, hφ₁]
    rw [h₂]
    positivity
  sorry

theorem XPgt0 {P : ℝ³} {ε θ θ_ φ φ_ : ℝ} (hP : ‖P‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hX : √2 * ε < ⟪vecX θ_ φ_, P⟫) :
    0 < ⟪vecX θ φ, P⟫ := by
  have h₁ : ‖⟪vecX θ_ φ_ - vecX θ φ, P⟫‖ ≤ ‖vecX θ_ φ_ - vecX θ φ‖ * ‖P‖ := by
    exact norm_inner_le_norm (vecX θ_ φ_ - vecX θ φ) P
  grw [inner_sub_left, ←Real.le_norm_self] at h₁
  rw [tsub_le_iff_tsub_le] at h₁
  have h₂ := norm_X_sub_lt hε hθ hφ
  grw [← h₁]
  rw [norm_sub_rev] at h₂
  have h₃ : ‖vecX θ_ φ_ - vecX θ φ‖ * ‖P‖ ≤ ‖vecX θ_ φ_ - vecX θ φ‖ * 1 :=
     mul_le_mul_of_nonneg_left hP (norm_nonneg _)
  linarith

theorem norm_M_apply_gt {ε r θ θ_ φ φ_ : ℝ} {P : ℝ³}
    (hP : ‖P‖ ≤ 1) (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hM : r + √2 * ε < ‖rotM θ_ φ_ P‖) : r < ‖rotM θ φ P‖ := by
  have h₁ : ‖rotM θ_ φ_ P‖ - ‖rotM θ φ - rotM θ_ φ_‖ * ‖P‖ ≤ ‖rotM θ φ P‖ := by
    grw [←ContinuousLinearMap.le_opNorm, ContinuousLinearMap.sub_apply]
    suffices ‖(rotM θ_ φ_) P‖ ≤ ‖(rotM θ φ) P‖ + ‖(rotM θ φ) P - (rotM θ_ φ_) P‖ by linarith
    exact norm_le_insert ((rotM θ φ) P) ((rotM θ_ φ_) P)
  have h₂ := norm_M_sub_lt hε hθ hφ
  grw [hP, mul_one] at h₁
  linarith

theorem norm_RM_sub_RM_le {ε θ θ_ φ φ_ α α_}
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) (hα : |α - α_| ≤ ε) :
    ‖rotprojRM θ φ α - rotprojRM θ_ φ_ α_‖ < √5 * ε := by
  sorry
