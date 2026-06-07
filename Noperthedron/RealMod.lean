import Mathlib.Analysis.RCLike.Basic

noncomputable
def Real.emod (a b : ℝ) : ℝ := Int.fract (a / b) * b

theorem Real.emod_in_interval {a b : ℝ} (hb : 0 < b) : Real.emod a b ∈ Set.Ico 0 b := by
  simp [emod]
  refine ⟨mul_nonneg (Int.fract_nonneg (a / b)) (le_of_lt hb), ?_⟩
  simpa using mul_lt_mul_of_pos_right (Int.fract_lt_one (a / b)) hb

theorem Real.emod_exists_multiple (a b : ℝ) (hb : 0 < b) : ∃ k : ℤ, Real.emod a b = a + k * b := by
  simp only [Real.emod]
  rw [← Int.self_sub_floor]
  use -⌊a / b⌋
  push_cast
  field_simp
  ring_nf
