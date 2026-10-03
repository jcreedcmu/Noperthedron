module

public import Noperthedron.Nopert231.IcoField
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# The snub dodecahedron's constant ξ

The snub dodecahedron's coordinates use ξ, the real root of ξ³ − 2ξ = φ
(φ the golden ratio; ξ ≈ 1.7155615). `snubXi` is that root, obtained from the
intermediate value theorem on a rational interval; `snubXi_unique` shows it is
the only real root, so the definition does not depend on the choice; and
`snubXi_bounds` encloses it in an interval of width 10⁻²⁴ (from the rational
bounds on √5 in `IcoField`).
-/

namespace Noperthedron.Nopert231

open IcoZ

/-- The golden ratio, (1 + √5)/2. -/
noncomputable def snubPhi : ℝ := (1 + sqrt5) / 2

noncomputable def snubCubic (x : ℝ) : ℝ := x ^ 3 - 2 * x - snubPhi

def xiLo : ℚ := 1715561499697367834681278 / 10 ^ 24
def xiHi : ℚ := 1715561499697367834681279 / 10 ^ 24

theorem snubCubic_xiLo_neg : snubCubic (xiLo : ℝ) < 0 := by
  obtain ⟨h5lo, -⟩ := sqrt5_bounds
  unfold snubCubic snubPhi
  have : ((xiLo : ℚ) : ℝ) ^ 3 - 2 * (xiLo : ℝ) - (1 + (sqrt5Lo : ℝ)) / 2 < 0 := by
    norm_num [xiLo, sqrt5Lo]
  linarith

theorem snubCubic_xiHi_pos : 0 < snubCubic (xiHi : ℝ) := by
  obtain ⟨-, h5hi⟩ := sqrt5_bounds
  unfold snubCubic snubPhi
  have : 0 < ((xiHi : ℚ) : ℝ) ^ 3 - 2 * (xiHi : ℝ) - (1 + (sqrt5Hi : ℝ)) / 2 := by
    norm_num [xiHi, sqrt5Hi]
  linarith

theorem exists_snubCubic_root :
    ∃ x ∈ Set.Icc (xiLo : ℝ) (xiHi : ℝ), snubCubic x = 0 := by
  have hcont : ContinuousOn snubCubic (Set.Icc (xiLo : ℝ) (xiHi : ℝ)) := by
    unfold snubCubic
    fun_prop
  have hle : (xiLo : ℝ) ≤ xiHi := by norm_num [xiLo, xiHi]
  exact intermediate_value_Icc hle hcont ⟨snubCubic_xiLo_neg.le, snubCubic_xiHi_pos.le⟩

/-- ξ: the real root of ξ³ − 2ξ = φ. -/
noncomputable def snubXi : ℝ := Classical.choose exists_snubCubic_root

theorem snubXi_bounds : (xiLo : ℝ) ≤ snubXi ∧ snubXi ≤ xiHi :=
  (Classical.choose_spec exists_snubCubic_root).1

theorem snubXi_cubic : snubXi ^ 3 - 2 * snubXi = snubPhi := by
  have h := (Classical.choose_spec exists_snubCubic_root).2
  unfold snubCubic at h
  change snubXi ^ 3 - 2 * snubXi - snubPhi = 0 at h
  linarith

/-- ξ is the only real root of x³ − 2x = φ. -/
theorem snubXi_unique {x : ℝ} (hx : x ^ 3 - 2 * x = snubPhi) : x = snubXi := by
  obtain ⟨hlo, hhi⟩ := snubXi_bounds
  have hxi := snubXi_cubic
  have hphi : (8 / 5 : ℝ) < snubPhi := by
    obtain ⟨h5lo, -⟩ := sqrt5_bounds
    unfold snubPhi
    norm_num [sqrt5Lo] at h5lo
    linarith
  have hlo' : (17 / 10 : ℝ) ≤ snubXi := le_trans (by norm_num [xiLo]) hlo
  -- x³ − 2x − φ = (x − ξ)(x² + ξx + ξ² − 2), and the quadratic factor is positive
  -- (discriminant ξ² − 4(ξ² − 2) = 8 − 3ξ² < 0 for ξ ≥ 1.7).
  have hfactor : (x - snubXi) * (x ^ 2 + snubXi * x + snubXi ^ 2 - 2) = 0 := by
    linear_combination hx - hxi
  have hq : 0 < x ^ 2 + snubXi * x + snubXi ^ 2 - 2 := by
    nlinarith [sq_nonneg (2 * x + snubXi), hlo']
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

end Noperthedron.Nopert231
