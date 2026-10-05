module

public import Noperthedron.PentagonalHexecontahedron.CapChartEval

@[expose] public section

/-!
# Covering the cap domain by the charts (real lemmas)

The decompositions behind the chart covering of a cap (nopert229
`capcert.cc`):

* `view_side`: a tangent offset (t₁, t₂) is m (A + τ B) for one of the four
  sides (A, B) ∈ {(e₁, e₂), (−e₁, e₂), (e₂, e₁), (−e₂, e₁)}, with
  m = max(|t₁|, |t₂|) and |τ| ≤ 1.
* `weighted_cube`: with weights w_i ∈ {1, 2} and ranges R_i > 0, a point (m, ω)
  with m ∈ [0, μ₀] and |ω_i| ≤ R_i μ₀^{w_i} is (μ, e, s) with μ ∈ [0, μ₀],
  m = μ e, ω_i = μ^{w_i} s_i, |s_i| ≤ R_i, and either e = 1 (the F_e chart) or
  e ∈ [0, 1] and |s_k| = R_k for some k (the face charts).
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

/-- The side's (A, B) in the (e₁, e₂) coordinates. -/
def sideA : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

def sideB : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | _ => (1, 0)

theorem view_side (t₁ t₂ : ℝ) : ∃ side < 4, ∃ m τ : ℝ, m = max |t₁| |t₂| ∧ |τ| ≤ 1 ∧
    t₁ = m * ((sideA side).1 + τ * (sideB side).1) ∧ t₂ = m * ((sideA side).2 + τ * (sideB side).2) := by
  rcases le_total |t₂| |t₁| with h | h
  · have hm : max |t₁| |t₂| = |t₁| := max_eq_left h
    rcases eq_or_ne t₁ 0 with h0 | h0
    · refine ⟨0, by norm_num, 0, 0, ?_, by norm_num, ?_, ?_⟩
      · rw [hm, h0, abs_zero]
      · simp [h0]
      · have : |t₂| = 0 := le_antisymm (by rw [h0, abs_zero] at h; exact h) (abs_nonneg _)
        simp [abs_eq_zero.mp this]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · refine ⟨1, by norm_num, -t₁, t₂ / -t₁, ?_, ?_, ?_, ?_⟩
      · rw [hm, abs_of_neg hneg]
      · rw [abs_div, abs_neg, div_le_one (abs_pos.mpr h0)]; exact h
      · simp [sideA, sideB]
      · simp [sideA, sideB]; field_simp
    · refine ⟨0, by norm_num, t₁, t₂ / t₁, ?_, ?_, ?_, ?_⟩
      · rw [hm, abs_of_pos hpos]
      · rw [abs_div, div_le_one (abs_pos.mpr h0)]; exact h
      · simp [sideA, sideB]
      · simp [sideA, sideB]; field_simp
  · have hm : max |t₁| |t₂| = |t₂| := max_eq_right h
    rcases eq_or_ne t₂ 0 with h0 | h0
    · refine ⟨2, by norm_num, 0, 0, ?_, by norm_num, ?_, ?_⟩
      · rw [hm, h0, abs_zero]
      · have : |t₁| = 0 := le_antisymm (by rw [h0, abs_zero] at h; exact h) (abs_nonneg _)
        simp [abs_eq_zero.mp this]
      · simp [h0]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · refine ⟨3, by norm_num, -t₂, t₁ / -t₂, ?_, ?_, ?_, ?_⟩
      · rw [hm, abs_of_neg hneg]
      · rw [abs_div, abs_neg, div_le_one (abs_pos.mpr h0)]; exact h
      · simp [sideA, sideB]; field_simp
      · simp [sideA, sideB]
    · refine ⟨2, by norm_num, t₂, t₁ / t₂, ?_, ?_, ?_, ?_⟩
      · rw [hm, abs_of_pos hpos]
      · rw [abs_div, div_le_one (abs_pos.mpr h0)]; exact h
      · simp [sideA, sideB]; field_simp
      · simp [sideA, sideB]

/-- The weighted radius of one coordinate: |ω|/R (weight 1) or √(|ω|/R) (weight 2). -/
noncomputable def wrad (wt : ℕ) (R ω : ℝ) : ℝ := if wt = 1 then |ω| / R else Real.sqrt (|ω| / R)

theorem wrad_nonneg (wt : ℕ) {R : ℝ} (hR : 0 < R) (ω : ℝ) : 0 ≤ wrad wt R ω := by
  unfold wrad; split_ifs
  · exact div_nonneg (abs_nonneg _) hR.le
  · exact Real.sqrt_nonneg _

/-- |ω| ≤ R μ^w iff the weighted radius is ≤ μ (μ ≥ 0, w ∈ {1, 2}). -/
theorem abs_le_iff_wrad_le (wt : ℕ) (hw : wt = 1 ∨ wt = 2) {R : ℝ} (hR : 0 < R) (ω : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    |ω| ≤ R * μ ^ wt ↔ wrad wt R ω ≤ μ := by
  unfold wrad
  rcases hw with rfl | rfl
  · simp only [if_true, pow_one]
    rw [div_le_iff₀ hR, mul_comm]
  · simp only [show (2 : ℕ) ≠ 1 by norm_num, if_false]
    rw [Real.sqrt_le_left hμ, div_le_iff₀ hR, mul_comm]

/-- |ω| = R (wrad)^w. -/
theorem abs_eq_wrad_pow (wt : ℕ) (hw : wt = 1 ∨ wt = 2) {R : ℝ} (hR : 0 < R) (ω : ℝ) :
    |ω| = R * wrad wt R ω ^ wt := by
  unfold wrad
  rcases hw with rfl | rfl
  · simp only [if_true, pow_one]; field_simp
  · simp only [show (2 : ℕ) ≠ 1 by norm_num, if_false]
    rw [Real.sq_sqrt (div_nonneg (abs_nonneg _) hR.le)]; field_simp

theorem weighted_cube (wt : Fin 3 → ℕ) (hw : ∀ i, wt i = 1 ∨ wt i = 2) (R : Fin 3 → ℝ) (hR : ∀ i, 0 < R i)
    (μ₀ m : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ μ₀) (ω : Fin 3 → ℝ) (hω : ∀ i, |ω i| ≤ R i * μ₀ ^ wt i) :
    ∃ μ e : ℝ, ∃ s : Fin 3 → ℝ, 0 ≤ μ ∧ μ ≤ μ₀ ∧ 0 ≤ e ∧ e ≤ 1 ∧ m = μ * e ∧
      (∀ i, ω i = μ ^ wt i * s i ∧ |s i| ≤ R i) ∧ (e = 1 ∨ ∃ k, |s k| = R k) := by
  set ρ : Fin 3 → ℝ := fun i => wrad (wt i) (R i) (ω i)
  have hρ0 : ∀ i, 0 ≤ ρ i := fun i => wrad_nonneg _ (hR i) _
  set μ := max m (max (ρ 0) (max (ρ 1) (ρ 2)))
  have hμ0 : 0 ≤ μ := le_trans hm0 (le_max_left _ _)
  have hρμ : ∀ i, ρ i ≤ μ := by
    intro i
    fin_cases i
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hμ0' : 0 ≤ μ₀ := le_trans hm0 hm1
  have hρμ₀ : ∀ i, ρ i ≤ μ₀ := fun i => (abs_le_iff_wrad_le _ (hw i) (hR i) _ hμ0').mp (hω i)
  have hμμ₀ : μ ≤ μ₀ := max_le hm1 (max_le (hρμ₀ 0) (max_le (hρμ₀ 1) (hρμ₀ 2)))
  rcases eq_or_lt_of_le hμ0 with hz | hpos
  · -- μ = 0: m = 0 and ω = 0.
    have hm : m = 0 := le_antisymm (hz ▸ le_max_left _ _) hm0
    have hωz : ∀ i, ω i = 0 := by
      intro i
      have := (abs_le_iff_wrad_le _ (hw i) (hR i) (ω i) hμ0).mpr (hρμ i)
      rw [← hz, zero_pow (by rcases hw i with h | h <;> omega), mul_zero] at this
      exact abs_nonpos_iff.mp this
    refine ⟨0, 1, fun _ => 0, le_refl _, hμ0', zero_le_one, le_refl _, by rw [hm]; ring, ?_, Or.inl rfl⟩
    intro i
    exact ⟨by rw [hωz i]; ring, by simp [(hR i).le]⟩
  · refine ⟨μ, m / μ, fun i => ω i / μ ^ wt i, hμ0, hμμ₀, div_nonneg hm0 hμ0,
      (div_le_one hpos).mpr (le_max_left _ _), by field_simp, ?_, ?_⟩
    · intro i
      have hpow : 0 < μ ^ wt i := pow_pos hpos _
      refine ⟨by field_simp, ?_⟩
      rw [abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
      exact (abs_le_iff_wrad_le _ (hw i) (hR i) (ω i) hμ0).mpr (hρμ i)
    · -- μ is m or one of the ρ_k.
      have face_of_eq : ∀ k, μ = ρ k → |ω k / μ ^ wt k| = R k := by
        intro k hk
        have hpow : 0 < μ ^ wt k := pow_pos hpos _
        rw [abs_div, abs_of_pos hpow, abs_eq_wrad_pow _ (hw k) (hR k), ← show ρ k = wrad (wt k) (R k) (ω k) from rfl,
          ← hk]
        field_simp
      have hcases : μ = m ∨ μ = ρ 0 ∨ μ = ρ 1 ∨ μ = ρ 2 := by
        simp only [μ, max_def]
        split_ifs <;> simp
      rcases hcases with h | h | h | h
      · left; rw [← h]; field_simp
      all_goals right
      · exact ⟨0, face_of_eq 0 h⟩
      · exact ⟨1, face_of_eq 1 h⟩
      · exact ⟨2, face_of_eq 2 h⟩

end Noperthedron.PentagonalHexecontahedron.Cap
