import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.SparseLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.PackedLocalViewTree
open AtlasProjectiveLocalViewTree
open AtlasProjectiveLocalCertificate

def log (msg : String) : IO Unit := do
  IO.println msg
  (← IO.getStdout).flush

def main : IO Unit := do
  let path := ".artifacts/nopert229/packs/code_48_tri_1.pack"
  let bytes ← IO.FS.readBinFile path
  let table := decodePackedCodeTriangle bytes
  let row := table.get 10296
  match row with
  | .decomposed id box coreAx defect0 D0 r_min c_cone c_core lam w =>
      log s!"Row 10296 diagnostics:"
      log s!"  r_min_nonneg: {decide (0 ≤ r_min)}"
      log s!"  r_nonneg: {decide (0 ≤ box.r)}"
      log s!"  r_le_two: {decide (box.r ≤ 2)}"
      log s!"  delta_nonneg: {decide (0 ≤ box.δ)}"
      log s!"  c_nonneg: {decide (0 ≤ box.c)}"
      log s!"  bary: {decide (box.decomposedBarycentricValid c_cone)}"
      log s!"  D0_nonneg: {decide (0 ≤ D0)}"
      log s!"  defect0_nonneg: {decide (∀ i, 0 ≤ defect0 i)}"
      log s!"  defect_budget0: {decide ((∑ i, box.weightUpper 0 i * defect0 i) ≤ D0)}"
      log s!"  c_cone_margin: {decide (box.δ ≤ c_cone)}"
      log s!"  annular_dominance: {decide (((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤ r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) * ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2))}"
      log s!"  B_pos: {decide (∀ j, 0 < (box.certificate j).B)}"
      log s!"  var: {decide (∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)}"
      log s!"  supp: {decide (∀ j i k, box.supportUpper j i k ≤ if j = 0 then defect0 i else 0)}"
      log s!"  dir_nonzero: {decide (∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)}"
      log s!"  budget: {decide (∀ j, box.weightBudget j ≤ (box.certificate j).B)}"
      log s!"  weight_nonneg: {decide (∀ j i, 0 ≤ box.weightLower j i)}"
      log s!"  weight_pos: {decide (∀ j, ∃ i, 0 < box.weightLower j i)}"
      log s!"  comp_angle: {decide (box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2)}"
      log s!"  c_core_margin: {decide (box.δ ≤ c_core)}"
      log s!"  core_B_pos: {decide (0 < coreAx.B)}"
      log s!"  core_var: {decide ((box.withCoreAxis coreAx c_core r_min).variationRadiusSum 0 + 3 * variationError ≤ coreAx.B * box.δ)}"
      log s!"  core_supp: {decide (∀ i k, (box.withCoreAxis coreAx c_core r_min).supportUpper 0 i k ≤ 0)}"
      log s!"  core_dir: {decide (∀ i, (box.withCoreAxis coreAx c_core r_min).supportUpper 0 i (coreAx.nonzeroWitness i) < 0)}"
      log s!"  core_budget: {decide ((box.withCoreAxis coreAx c_core r_min).weightBudget 0 ≤ coreAx.B)}"
      log s!"  core_weight_nonneg: {decide (∀ i, 0 ≤ (box.withCoreAxis coreAx c_core r_min).weightLower 0 i)}"
      log s!"  core_weight_pos: {decide (∃ i, 0 < (box.withCoreAxis coreAx c_core r_min).weightLower 0 i)}"
      log s!"  core_angle: {decide (r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2)}"
      log s!"  c_cone_pos: {decide (0 < c_cone)}"
      log s!"  c_margin: {decide (box.δ ≤ box.c)}"
      log s!"  c_sum_pos: {decide (0 < box.c + box.δ)}"
      log s!"  hdecomp: {decide ((box.withCoreAxis coreAx c_core r_min).approxNormalizedCenter 0 = lam • box.approxNormalizedCenter 0 + w)}"
      log s!"  hortho: {decide ((∑ i, (box.approxNormalizedCenter 0 i) * (w i)) = 0)}"
      log s!"  hu_pos: {decide (0 < (∑ i, (box.approxNormalizedCenter 0 i) ^ 2))}"
      log s!"  hw_pos: {decide (0 < (∑ i, (w i) ^ 2))}"
      log s!"  hlam_nonneg: {decide (0 ≤ lam)}"
      log s!"  hc_cone_nonneg: {decide (0 ≤ c_cone)}"
      log s!"  hmargin: {decide (0 ≤ lam * c_cone - c_core)}"
      log s!"  hineq: {decide ((∑ i, (w i) ^ 2) * ((∑ i, (box.approxNormalizedCenter 0 i) ^ 2) - c_cone^2) ≤ (∑ i, (box.approxNormalizedCenter 0 i) ^ 2) * (lam * c_cone - c_core)^2)}"
  | _ => log "Not decomposed!"
