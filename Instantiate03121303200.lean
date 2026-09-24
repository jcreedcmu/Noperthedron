import Noperthedron.Nopert229.TestEvalRealCage
import Noperthedron.Nopert229.TestFlockTheorem

open Noperthedron Noperthedron.Nopert229
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveLocalCertificate
open AtlasProjectiveView

namespace Noperthedron.Nopert229

def box260 : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := 300 / 1000000
  δ := 260 / 1000000
  r := 4 / 100000

-- 5 Core Flock Axes covering the cone with margin c_core >= 15 / 10000
def coreAx0 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 800, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 578456463/1000000000
}

def coreAx1 : AxisCertificate := {
  edgeStart := ![2, 10, 19],
  edgeFinish := ![1, 15, 3],
  edgeStart₂ := ![1, 15, 3],
  edgeFinish₂ := ![4, 19, 2],
  mix := ![0, 800, 200],
  index := ![1, 15, 3],
  nonzeroWitness := ![15, 1, 9],
  B := 96698479/50000000
}

def coreAx2 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 1000, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 519773829/1000000000
}

def coreAx3 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 333, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 519773829/1000000000
}

def coreAx4 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 666, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 38424249/50000000
}

def flockAxes : Fin 5 → AxisCertificate :=
  fun | 0 => coreAx0
      | 1 => coreAx1
      | 2 => coreAx2
      | 3 => coreAx3
      | 4 => coreAx4

def defect0 : Fin 3 → ℚ := fun
  | 0 => 0
  | 1 => 0
  | 2 => 205 / 1000000

def D0 : ℚ := 736 / 10000000
def c_cone : ℚ := 25 / 1000
def c_core : ℚ := 15 / 10000
def r_min : ℚ := 23 / 10000

theorem h_r_min_nonneg : 0 ≤ r_min := by decide +kernel
theorem h_r_nonneg : 0 ≤ box260.r := by decide +kernel
theorem h_r_le_two : box260.r ≤ 2 := by decide +kernel
theorem h_mismatch : box260.mismatchRadius ≤ box260.r := by decide +kernel
theorem h_delta_nonneg : 0 ≤ box260.δ := by decide +kernel
theorem h_c_nonneg : 0 ≤ box260.c := by decide +kernel
theorem h_bary : box260.decomposedBarycentricValid c_cone := by decide +kernel
theorem h_D0_nonneg : 0 ≤ D0 := by decide +kernel
theorem h_defect0_nonneg : ∀ i, 0 ≤ defect0 i := by decide +kernel

theorem h_defect_budget0 : (∑ i, box260.weightUpper 0 i * defect0 i) ≤ D0 := by
  have hsum : (∑ i, box260.weightUpper 0 i * defect0 i) =
      box260.weightUpper 0 0 * 0 +
      box260.weightUpper 0 1 * 0 +
      box260.weightUpper 0 2 * (205 / 1000000) := by
    rw [Fin.sum_univ_three]
    dsimp [defect0]
  rw [hsum]
  have h_le : box260.weightUpper 0 2 ≤ 359 / 1000 := by decide +kernel
  have h_nonneg : 0 ≤ box260.weightUpper 0 2 := by decide +kernel
  dsimp [D0]
  linarith

theorem h_c_cone_margin : box260.δ ≤ c_cone := by decide +kernel

theorem h_annular_dominance :
    ((1/2 : ℚ) * box260.r^2 * (box260.certificate 0).B + D0)^2 ≤
    r_min^2 * (1 - (1/4 : ℚ)*box260.r^2) * ((c_cone - box260.δ)^2 * (box260.certificate 0).B^2) := by
  have hB : (box260.certificate 0).B = 349290553 / 250000000 := rfl
  rw [hB]
  decide +kernel

theorem h_B_pos : ∀ j, 0 < (box260.certificate j).B := by decide +kernel
theorem h_var : ∀ j, box260.variationRadiusSum j + 3 * variationError ≤ (box260.certificate j).B * box260.δ := by decide +kernel

theorem h_supp : ∀ j i k, box260.supportUpper j i k ≤ if j = 0 then defect0 i else 0 := by
  intro j i k
  fin_cases j
  · fin_cases i
    · fin_cases k <;> decide +kernel
    · fin_cases k <;> decide +kernel
    · fin_cases k <;> decide +kernel
  · fin_cases i <;> fin_cases k <;> decide +kernel
  · fin_cases i <;> fin_cases k <;> decide +kernel
  · fin_cases i <;> fin_cases k <;> decide +kernel

theorem h_dir_nonzero : ∀ j i, box260.supportUpper j i ((box260.certificate j).nonzeroWitness i) < 0 := by
  intro j i
  fin_cases j <;> fin_cases i <;> decide +kernel

theorem h_budget : ∀ j, box260.weightBudget j ≤ (box260.certificate j).B := by
  intro j; fin_cases j <;> decide +kernel

theorem h_weight_nonneg : ∀ j i, 0 ≤ box260.weightLower j i := by
  intro j i; fin_cases j <;> fin_cases i <;> decide +kernel

theorem h_weight_pos : ∀ j, ∃ i, 0 < box260.weightLower j i := by
  intro j
  fin_cases j
  · use 0; decide +kernel
  · use 0; decide +kernel
  · use 0; decide +kernel
  · use 0; decide +kernel

theorem h_comp_angle : box260.r^2 * (1 + (box260.c - box260.δ)^2) ≤ 4 * (box260.c - box260.δ)^2 := by norm_num [box260]
theorem h_c_core_margin : box260.δ ≤ c_core := by decide +kernel

theorem h_core_B_pos : ∀ m : Fin 5, 0 < (flockAxes m).B := by
  intro m; fin_cases m <;> decide +kernel

theorem h_core_var : ∀ m : Fin 5,
    (box260.withCoreAxis (flockAxes m) c_core r_min).variationRadiusSum 0 + 3 * variationError ≤
      (flockAxes m).B * box260.δ := by
  intro m; fin_cases m <;> decide +kernel

theorem h_core_supp : ∀ (m : Fin 5) i k,
    (box260.withCoreAxis (flockAxes m) c_core r_min).supportUpper 0 i k ≤ 0 := by
  intro m i k
  fin_cases m <;> fin_cases i <;> fin_cases k <;> decide +kernel

theorem h_core_dir : ∀ (m : Fin 5) i,
    (box260.withCoreAxis (flockAxes m) c_core r_min).supportUpper 0 i ((flockAxes m).nonzeroWitness i) < 0 := by
  intro m i
  fin_cases m <;> fin_cases i <;> decide +kernel

theorem h_core_budget : ∀ m : Fin 5,
    (box260.withCoreAxis (flockAxes m) c_core r_min).weightBudget 0 ≤ (flockAxes m).B := by
  intro m; fin_cases m <;> decide +kernel

theorem h_core_weight_nonneg : ∀ (m : Fin 5) i,
    0 ≤ (box260.withCoreAxis (flockAxes m) c_core r_min).weightLower 0 i := by
  intro m i; fin_cases m <;> fin_cases i <;> decide +kernel

theorem h_core_weight_pos : ∀ m : Fin 5,
    ∃ i, 0 < (box260.withCoreAxis (flockAxes m) c_core r_min).weightLower 0 i := by
  intro m
  fin_cases m
  · use 0; decide +kernel
  · use 0; decide +kernel
  · use 0; decide +kernel
  · use 0; decide +kernel
  · use 0; decide +kernel

theorem h_core_angle : r_min ^ 2 * (1 + (c_core - box260.δ) ^ 2) ≤ 4 * (c_core - box260.δ) ^ 2 := by
  decide +kernel

theorem h_c_cone_pos : 0 < c_cone := by decide +kernel
theorem h_c_margin : box260.δ ≤ box260.c := by decide +kernel
theorem h_c_sum_pos : 0 < box260.c + box260.δ := by decide +kernel

/-- Main theorem: Discharging ¬ RupertPose for Triangle 03121303200 via Decomposed Flock. -/
theorem triangle_03121303200_not_rupert
    (hexc_covers : ∀ axis, ‖axis‖ = 1 → (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box260.approxNormalizedCenter 0)) →
      ∃ m : Fin 5, (c_core : ℝ) ≤ inner ℝ axis (toR3 ((box260.withCoreAxis (flockAxes m) c_core r_min).approxNormalizedCenter 0)))
    {p : AtlasPose ℝ} (hp : p ∈ box260.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box260.root p)
    (hmem : InTriangle (toReal box260.triangle)
      (AtlasProjectiveView.normalizedView box260.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box260.chart offset) exactPolyhedron.hull := by
  apply valid_imp_not_translated_rupert_of_flock_decomposed box260 5 flockAxes defect0 D0 r_min c_cone c_core
    h_r_min_nonneg h_r_nonneg h_r_le_two h_mismatch h_delta_nonneg h_c_nonneg h_bary
    h_D0_nonneg h_defect0_nonneg h_defect_budget0 h_c_cone_margin h_annular_dominance
    h_B_pos h_var h_supp h_dir_nonzero h_budget h_weight_nonneg h_weight_pos h_comp_angle
    h_c_core_margin h_core_B_pos h_core_var h_core_supp h_core_dir h_core_budget
    h_core_weight_nonneg h_core_weight_pos h_core_angle hexc_covers h_c_cone_pos
    h_c_margin h_c_sum_pos hp offset hscale hmem

end Noperthedron.Nopert229
