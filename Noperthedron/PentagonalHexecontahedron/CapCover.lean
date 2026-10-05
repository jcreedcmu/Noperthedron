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

/-- The cone charts: a point within t₀ Rᵢ/2 of the center in every coordinate is
c + (Rᵢ/2) t σ with t ∈ [0, t₀] and σ on a face of the unit cube (|σ_k| = 1, |σᵢ| ≤ 1). -/
theorem cone_decomp (R : Fin 3 → ℝ) (hR : ∀ i, 0 < R i) (t₀ : ℝ) (c s : Fin 3 → ℝ)
    (hs : ∀ i, |s i - c i| ≤ t₀ * R i / 2) :
    ∃ t : ℝ, ∃ σ : Fin 3 → ℝ, ∃ k : Fin 3, 0 ≤ t ∧ t ≤ t₀ ∧ |σ k| = 1 ∧ (∀ i, |σ i| ≤ 1) ∧
      ∀ i, s i = c i + R i / 2 * t * σ i := by
  have hR2 : ∀ i, 0 < R i / 2 := fun i => by linarith [hR i]
  set ρ : Fin 3 → ℝ := fun i => |s i - c i| / (R i / 2)
  have hρ0 : ∀ i, 0 ≤ ρ i := fun i => div_nonneg (abs_nonneg _) (hR2 i).le
  have hρt : ∀ i, ρ i ≤ t₀ := fun i => by
    rw [div_le_iff₀ (hR2 i)]; linarith [hs i]
  set t := max (ρ 0) (max (ρ 1) (ρ 2))
  have hρle : ∀ i, ρ i ≤ t := by
    intro i; fin_cases i
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have ht0 : 0 ≤ t := le_trans (hρ0 0) (hρle 0)
  have htt : t ≤ t₀ := max_le (hρt 0) (max_le (hρt 1) (hρt 2))
  rcases eq_or_lt_of_le ht0 with hz | hpos
  · -- t = 0: s = c.
    have hsc : ∀ i, s i = c i := by
      intro i
      have h := hρle i
      rw [← hz] at h
      have : |s i - c i| / (R i / 2) = 0 := le_antisymm h (hρ0 i)
      rw [div_eq_zero_iff] at this
      rcases this with h1 | h1
      · linarith [abs_eq_zero.mp h1]
      · linarith [hR2 i]
    refine ⟨0, fun i => if i = 0 then 1 else 0, 0, le_refl _, hz ▸ htt, by simp, ?_, ?_⟩
    · intro i; by_cases h : i = 0 <;> simp [h]
    · intro i; rw [hsc i]; ring
  · refine ⟨t, fun i => (s i - c i) / (R i / 2 * t), ?_⟩
    have hcases : t = ρ 0 ∨ t = ρ 1 ∨ t = ρ 2 := by
      simp only [t, max_def]; split_ifs <;> simp
    have hk : ∃ k, t = ρ k := by
      rcases hcases with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    obtain ⟨k, hk⟩ := hk
    refine ⟨k, ht0, htt, ?_, ?_, ?_⟩
    · have hpos' : 0 < R k / 2 * t := mul_pos (hR2 k) hpos
      have hne : |s k - c k| ≠ 0 := by
        intro h0
        have : ρ k = 0 := by simp [ρ, h0]
        linarith
      have hRk : R k ≠ 0 := (hR k).ne'
      rw [abs_div, abs_of_pos hpos', hk]
      simp only [ρ]
      field_simp
    · intro i
      have hpos' : 0 < R i / 2 * t := mul_pos (hR2 i) hpos
      rw [abs_div, abs_of_pos hpos', div_le_one hpos']
      have := hρle i
      simp only [ρ] at this
      rw [div_le_iff₀ (hR2 i)] at this
      linarith
    · intro i
      have hpos' : 0 < R i / 2 * t := mul_pos (hR2 i) hpos
      have := hpos'.ne'
      have hRi : R i ≠ 0 := (hR i).ne'
      field_simp
      ring

/-- The ratio blow-up of one weak coordinate: |v| ≤ Z μ (inner: v = μ v', |v'| ≤ Z) or
v = ±(Z μ + v') with v' ∈ [0, B] (outer), when |v| ≤ B and μ ≥ 0. -/
theorem ratio_decomp (Z μ B v : ℝ) (hZ : 0 < Z) (hμ : 0 ≤ μ) (hv : |v| ≤ B) :
    (|v| ≤ Z * μ ∧ ∃ v', v = μ * v' ∧ |v'| ≤ Z) ∨
      ∃ sg : Bool, ∃ v', 0 ≤ v' ∧ v' ≤ B ∧ v = (if sg then 1 else -1) * (Z * μ + v') := by
  by_cases h : |v| ≤ Z * μ
  · left
    refine ⟨h, ?_⟩
    rcases eq_or_lt_of_le hμ with h0 | hpos
    · refine ⟨0, ?_, by simp [hZ.le]⟩
      rw [← h0, mul_zero] at h
      rw [← h0]; simpa using abs_nonpos_iff.mp h
    · refine ⟨v / μ, by field_simp, ?_⟩
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]; exact h
  · right
    push Not at h
    rcases le_or_gt 0 v with hv0 | hv0
    · refine ⟨true, v - Z * μ, ?_, ?_, ?_⟩
      · rw [abs_of_nonneg hv0] at h; linarith
      · rw [abs_of_nonneg hv0] at hv; nlinarith [mul_nonneg hZ.le hμ]
      · simp
    · refine ⟨false, -v - Z * μ, ?_, ?_, ?_⟩
      · rw [abs_of_neg hv0] at h; linarith
      · rw [abs_of_neg hv0] at hv; nlinarith [mul_nonneg hZ.le hμ]
      · simp

end Noperthedron.PentagonalHexecontahedron.Cap

namespace Noperthedron.PentagonalHexecontahedron.Cap

/-- (e, s₀) of tie-scheme chart m at (μ, p₀, p₁) (as `rTieES`). -/
noncomputable def tieE (m Z Z2 K Kp : ℕ) (μ p0 q : ℝ) : ℝ × ℝ :=
  let eK := (K : ℝ) * μ + p0
  if m = 10 then (μ * p0, μ * q)
  else if m = 11 then (μ * p0, (Kp : ℝ) * μ + q)
  else if m = 12 then (μ * p0, -((Kp : ℝ) * μ + q))
  else if m = 13 then (eK, μ * q)
  else if m = 14 then (eK, -((Z : ℝ) * μ + q))
  else if m = 15 then (eK, eK + μ * q)
  else if m = 16 then (eK, eK + (Z2 : ℝ) * μ + q)
  else (eK, (Z : ℝ) * μ + q * (p0 + ((K - Z - Z2 : ℕ) : ℝ) * μ))

/-- The bounds of (p₀, p₁) of tie-scheme chart m (as `tieLoHi`). -/
def tieBox (m Z Z2 K Kp : ℕ) : (ℚ × ℚ) × (ℚ × ℚ) :=
  ((if m ≤ 12 then (0, (K : ℚ)) else (0, 1)),
   (if m = 10 then (-(Kp : ℚ), (Kp : ℚ)) else if m = 13 then (-(Z : ℚ), (Z : ℚ))
     else if m = 15 then (-(Z2 : ℚ), (Z2 : ℚ)) else if m = 17 then (0, 1) else (0, 2)))

/-- Closes a tie-box bound goal. -/
macro "tie_bound" : tactic => `(tactic| (simp only [tieBox]; norm_num <;> first
  | linarith
  | positivity
  | (rw [div_le_iff₀ (by assumption)]; linarith)
  | (rw [le_div_iff₀ (by assumption)]; linarith)
  | nlinarith))

/-- Closes a tie-chart (e, s₀) goal. -/
macro "tie_eq" : tactic => `(tactic| (refine Prod.ext ?_ ?_ <;> simp [tieE] <;> (try field_simp) <;> (try ring)))

/-- **The tie scheme covers** every (μ, e, s₀) with μ ≥ 0, e ∈ [0, 1], |s₀| ≤ 2. -/
theorem tie_decomp (Z Z2 K Kp : ℕ) (hK : Z + Z2 ≤ K) (hKp : K < Kp)
    (μ e s0 : ℝ) (hμ : 0 ≤ μ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hs : |s0| ≤ 2) :
    ∃ m, 10 ≤ m ∧ m < 18 ∧ ∃ p0 p1 : ℝ,
      ((tieBox m Z Z2 K Kp).1.1 : ℝ) ≤ p0 ∧ p0 ≤ (tieBox m Z Z2 K Kp).1.2 ∧
      ((tieBox m Z Z2 K Kp).2.1 : ℝ) ≤ p1 ∧ p1 ≤ (tieBox m Z Z2 K Kp).2.2 ∧
      tieE m Z Z2 K Kp μ p0 p1 = (e, s0) := by
  have hZ : (0 : ℝ) ≤ Z := Nat.cast_nonneg _
  have hZ2 : (0 : ℝ) ≤ Z2 := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hKr : (Z : ℝ) + Z2 ≤ K := by exact_mod_cast hK
  have hKpr : (K : ℝ) < Kp := by exact_mod_cast hKp
  have hsub : ((K - Z - Z2 : ℕ) : ℝ) = K - Z - Z2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hZmu := mul_nonneg hZ hμ
  have hZ2mu := mul_nonneg hZ2 hμ
  have hKmu := mul_nonneg hK0 hμ
  rw [abs_le] at hs
  by_cases hA : e ≤ K * μ
  · rcases eq_or_lt_of_le hμ with h0 | hpos
    · subst h0
      have he : e = 0 := by simp at hA; linarith
      subst he
      rcases lt_trichotomy s0 0 with hn | hz | hp
      · refine ⟨12, by norm_num, by norm_num, 0, -s0, ?_, ?_, ?_, ?_, ?_⟩ <;> first | tie_bound | tie_eq
      · subst hz
        refine ⟨10, by norm_num, by norm_num, 0, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> first | tie_bound | tie_eq
      · refine ⟨11, by norm_num, by norm_num, 0, s0, ?_, ?_, ?_, ?_, ?_⟩ <;> first | tie_bound | tie_eq
    · have hε : e / μ ≤ K := by rw [div_le_iff₀ hpos]; linarith
      have hε0 : 0 ≤ e / μ := div_nonneg he0 hpos.le
      by_cases hB : |s0| ≤ Kp * μ
      · rw [abs_le] at hB
        refine ⟨10, by norm_num, by norm_num, e / μ, s0 / μ, ?_, ?_, ?_, ?_, ?_⟩ <;> first | tie_bound | tie_eq
      · rw [abs_le, not_and_or] at hB
        rcases hB with hB | hB
        · push Not at hB
          refine ⟨12, by norm_num, by norm_num, e / μ, -s0 - Kp * μ, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | tie_bound | tie_eq
        · push Not at hB
          refine ⟨11, by norm_num, by norm_num, e / μ, s0 - Kp * μ, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | tie_bound | tie_eq
  · push Not at hA
    have hp0 : 0 ≤ e - K * μ := by linarith
    have hp1 : e - K * μ ≤ 1 := by linarith
    by_cases hI : |s0| ≤ Z * μ
    · rw [abs_le] at hI
      rcases eq_or_lt_of_le hμ with h0 | hpos
      · subst h0
        have : s0 = 0 := by simp at hI; linarith
        subst this
        refine ⟨13, by norm_num, by norm_num, e, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> first | tie_bound | tie_eq
      · refine ⟨13, by norm_num, by norm_num, e - K * μ, s0 / μ, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | tie_bound | tie_eq
    · rw [abs_le, not_and_or] at hI
      rcases hI with hI | hI
      · push Not at hI
        refine ⟨14, by norm_num, by norm_num, e - K * μ, -s0 - Z * μ, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | tie_bound | tie_eq
      · push Not at hI
        by_cases hT : |s0 - e| ≤ Z2 * μ
        · rw [abs_le] at hT
          rcases eq_or_lt_of_le hμ with h0 | hpos
          · subst h0
            have : s0 = e := by simp at hT; linarith
            subst this
            refine ⟨15, by norm_num, by norm_num, s0, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> first | tie_bound | tie_eq
          · refine ⟨15, by norm_num, by norm_num, e - K * μ, (s0 - e) / μ, ?_, ?_, ?_, ?_, ?_⟩ <;>
              first | tie_bound | tie_eq
        · rw [abs_le, not_and_or] at hT
          rcases hT with hT | hT
          · push Not at hT
            have hD : s0 - Z * μ < e - (Z + Z2) * μ := by linarith
            have hDpos : 0 < e - (Z + Z2) * μ := by linarith
            refine ⟨17, by norm_num, by norm_num, e - K * μ, (s0 - Z * μ) / (e - (Z + Z2) * μ),
              ?_, ?_, ?_, ?_, ?_⟩
            · tie_bound
            · tie_bound
            · simp only [tieBox]; norm_num; exact div_nonneg (by linarith) hDpos.le
            · simp only [tieBox]; norm_num; exact (div_le_one hDpos).mpr hD.le
            · refine Prod.ext ?_ ?_
              · simp [tieE]
              · simp only [tieE]; norm_num
                rw [hsub, show e - K * μ + (K - Z - Z2) * μ = e - (Z + Z2) * μ by ring,
                  div_mul_cancel₀ _ hDpos.ne']
                ring
          · push Not at hT
            refine ⟨16, by norm_num, by norm_num, e - K * μ, s0 - e - Z2 * μ, ?_, ?_, ?_, ?_, ?_⟩ <;>
              first | tie_bound | tie_eq

end Noperthedron.PentagonalHexecontahedron.Cap
