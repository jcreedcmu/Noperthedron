import Noperthedron.SolutionTable.RationalLocalCheck.Precondition

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox (κ)

noncomputable section

/-!
### Basic computable checks

Small Bool-level checks extracted from the table row fields, together with soundness lemmas.
-/

def DENOM_Z : ℤ := 15360000

def FOUR_BOUND_Z : ℤ := 8 * DENOM_Z

lemma denom_z_cast : (DENOM_Z : ℝ) = DENOM := by
  norm_num [DENOM_Z, DENOM]

lemma two_denom_pos : (0 : ℝ) < 2 * DENOM := by
  norm_num [DENOM]

lemma four_bound_div_denom : (FOUR_BOUND_Z : ℝ) / (2 * DENOM) = 4 := by
  norm_num [FOUR_BOUND_Z, DENOM_Z, DENOM]

lemma four_bound_div_denom_neg : (-FOUR_BOUND_Z : ℝ) / (2 * DENOM) = -4 := by
  norm_num [FOUR_BOUND_Z, DENOM_Z, DENOM]

def Row.intervalMidNum (row : Row) (p : Param) : ℤ :=
  row.interval.min p + row.interval.max p

def Row.intervalWidth (row : Row) (p : Param) : ℤ :=
  row.interval.max p - row.interval.min p

lemma intervalMid_eq_midNum (row : Row) (p : Param) :
    row.intervalMid p = (row.intervalMidNum p : ℝ) / (2 * DENOM) := by
  simp [Row.intervalMid, Row.intervalMidNum]

lemma intervalHalfWidth_eq_width (row : Row) (p : Param) :
    row.intervalHalfWidth p = (row.intervalWidth p : ℝ) / (2 * DENOM) := by
  simp [Row.intervalHalfWidth, Row.intervalWidth]

lemma decide_true_iff {p : Prop} [Decidable p] : decide p = true → p := by
  intro h
  by_cases hp : p
  · exact hp
  · simp [hp] at h

lemma intervalMid_mem_fourInterval (row : Row) (p : Param)
    (h : (-FOUR_BOUND_Z ≤ row.intervalMidNum p) ∧ (row.intervalMidNum p ≤ FOUR_BOUND_Z)) :
    row.intervalMid p ∈ Set.Icc (-4 : ℝ) 4 := by
  have hlo' : (-FOUR_BOUND_Z : ℝ) ≤ (row.intervalMidNum p : ℝ) := by
    exact_mod_cast h.1
  have hhi' : (row.intervalMidNum p : ℝ) ≤ (FOUR_BOUND_Z : ℝ) := by
    exact_mod_cast h.2
  have hden : 0 ≤ (2 * DENOM : ℝ) := le_of_lt two_denom_pos
  have hlo : (-FOUR_BOUND_Z : ℝ) / (2 * DENOM) ≤
      (row.intervalMidNum p : ℝ) / (2 * DENOM) :=
    div_le_div_of_nonneg_right hlo' hden
  have hhi : (row.intervalMidNum p : ℝ) / (2 * DENOM) ≤
      (FOUR_BOUND_Z : ℝ) / (2 * DENOM) :=
    div_le_div_of_nonneg_right hhi' hden
  have hlo'' : (-4 : ℝ) ≤ row.intervalMid p := by
    simpa [intervalMid_eq_midNum, four_bound_div_denom_neg] using hlo
  have hhi'' : row.intervalMid p ≤ (4 : ℝ) := by
    simpa [intervalMid_eq_midNum, four_bound_div_denom] using hhi
  exact ⟨hlo'', hhi''⟩

def Row.localPoseInFourIntervalBool (row : Row) : Bool :=
  decide (
    (-FOUR_BOUND_Z ≤ row.intervalMidNum .θ₁ ∧ row.intervalMidNum .θ₁ ≤ FOUR_BOUND_Z) ∧
    (-FOUR_BOUND_Z ≤ row.intervalMidNum .θ₂ ∧ row.intervalMidNum .θ₂ ≤ FOUR_BOUND_Z) ∧
    (-FOUR_BOUND_Z ≤ row.intervalMidNum .φ₁ ∧ row.intervalMidNum .φ₁ ≤ FOUR_BOUND_Z) ∧
    (-FOUR_BOUND_Z ≤ row.intervalMidNum .φ₂ ∧ row.intervalMidNum .φ₂ ≤ FOUR_BOUND_Z) ∧
    (-FOUR_BOUND_Z ≤ row.intervalMidNum .α ∧ row.intervalMidNum .α ≤ FOUR_BOUND_Z))

lemma localPoseInFourIntervalBool_sound (row : Row) :
    row.localPoseInFourIntervalBool = true -> fourInterval.contains row.localPose := by
  intro h
  have h' :
      (-FOUR_BOUND_Z ≤ row.intervalMidNum .θ₁ ∧ row.intervalMidNum .θ₁ ≤ FOUR_BOUND_Z) ∧
      (-FOUR_BOUND_Z ≤ row.intervalMidNum .θ₂ ∧ row.intervalMidNum .θ₂ ≤ FOUR_BOUND_Z) ∧
      (-FOUR_BOUND_Z ≤ row.intervalMidNum .φ₁ ∧ row.intervalMidNum .φ₁ ≤ FOUR_BOUND_Z) ∧
      (-FOUR_BOUND_Z ≤ row.intervalMidNum .φ₂ ∧ row.intervalMidNum .φ₂ ≤ FOUR_BOUND_Z) ∧
      (-FOUR_BOUND_Z ≤ row.intervalMidNum .α ∧ row.intervalMidNum .α ≤ FOUR_BOUND_Z) :=
    decide_true_iff h
  rcases h' with ⟨hθ₁, hθ₂, hφ₁, hφ₂, hα⟩
  have hθ₁' := intervalMid_mem_fourInterval row .θ₁ hθ₁
  have hθ₂' := intervalMid_mem_fourInterval row .θ₂ hθ₂
  have hφ₁' := intervalMid_mem_fourInterval row .φ₁ hφ₁
  have hφ₂' := intervalMid_mem_fourInterval row .φ₂ hφ₂
  have hα' := intervalMid_mem_fourInterval row .α hα
  simp [PoseInterval.contains, Row.localPose] at hθ₁' hθ₂' hφ₁' hφ₂' hα' ⊢
  exact ⟨hθ₁', hθ₂', hφ₁', hφ₂', hα'⟩

def Row.localEpsPosBool (row : Row) : Bool :=
  decide (
    0 < row.intervalWidth .θ₁ ∨
    0 < row.intervalWidth .φ₁ ∨
    0 < row.intervalWidth .θ₂ ∨
    0 < row.intervalWidth .φ₂ ∨
    0 < row.intervalWidth .α)

lemma intervalHalfWidth_pos_of_width_pos (row : Row) (p : Param)
    (h : 0 < row.intervalWidth p) : 0 < row.intervalHalfWidth p := by
  have hpos : (0 : ℝ) < (row.intervalWidth p : ℝ) := by exact_mod_cast h
  have hden : (0 : ℝ) < 2 * DENOM := two_denom_pos
  simpa [intervalHalfWidth_eq_width] using (div_pos hpos hden)

lemma localEpsPosBool_sound (row : Row) :
    row.localEpsPosBool = true -> 0 < row.localEps := by
  intro h
  have h' :
      0 < row.intervalWidth .θ₁ ∨
      0 < row.intervalWidth .φ₁ ∨
      0 < row.intervalWidth .θ₂ ∨
      0 < row.intervalWidth .φ₂ ∨
      0 < row.intervalWidth .α :=
    decide_true_iff h
  rcases h' with hθ₁ | hφ₁ | hθ₂ | hφ₂ | hα
  · have hhalf : 0 < row.intervalHalfWidth .θ₁ :=
      intervalHalfWidth_pos_of_width_pos row .θ₁ hθ₁
    exact lt_of_lt_of_le hhalf (intervalHalfWidth_le_localEps row .θ₁)
  · have hhalf : 0 < row.intervalHalfWidth .φ₁ :=
      intervalHalfWidth_pos_of_width_pos row .φ₁ hφ₁
    exact lt_of_lt_of_le hhalf (intervalHalfWidth_le_localEps row .φ₁)
  · have hhalf : 0 < row.intervalHalfWidth .θ₂ :=
      intervalHalfWidth_pos_of_width_pos row .θ₂ hθ₂
    exact lt_of_lt_of_le hhalf (intervalHalfWidth_le_localEps row .θ₂)
  · have hhalf : 0 < row.intervalHalfWidth .φ₂ :=
      intervalHalfWidth_pos_of_width_pos row .φ₂ hφ₂
    exact lt_of_lt_of_le hhalf (intervalHalfWidth_le_localEps row .φ₂)
  · have hhalf : 0 < row.intervalHalfWidth .α :=
      intervalHalfWidth_pos_of_width_pos row .α hα
    exact lt_of_lt_of_le hhalf (intervalHalfWidth_le_localEps row .α)

def Row.localRPosBool (row : Row) : Bool :=
  decide (0 < row.r)

lemma localRPosBool_sound (row : Row) :
    row.localRPosBool = true -> 0 < row.localR := by
  intro h
  have hr : 0 < row.r := decide_true_iff h
  have hpos : (0 : ℝ) < (row.r : ℝ) := by exact_mod_cast hr
  have hden : (0 : ℝ) < R_DENOMINATOR := by norm_num [R_DENOMINATOR]
  simpa [Row.localR] using (div_pos hpos hden)

end

end Solution
