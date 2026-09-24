import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def coreAx0 : AxisCertificate := {
  edgeStart := ![2, 8, 19],
  edgeFinish := ![1, 9, 3],
  edgeStart₂ := ![1, 9, 3],
  edgeFinish₂ := ![4, 10, 2],
  mix := ![0, 800, 800],
  index := ![1, 9, 3],
  nonzeroWitness := ![15, 3, 9],
  B := 195319419 / 200000000
}

def coreAx1 : AxisCertificate := {
  edgeStart := ![2, 4, 19],
  edgeFinish := ![1, 8, 3],
  edgeStart₂ := ![1, 8, 3],
  edgeFinish₂ := ![4, 9, 2],
  mix := ![0, 200, 1000],
  index := ![1, 8, 3],
  nonzeroWitness := ![15, 3, 8],
  B := 896947911 / 1000000000
}

def coreAx2 : AxisCertificate := {
  edgeStart := ![2, 1, 15],
  edgeFinish := ![1, 4, 19],
  edgeStart₂ := ![1, 4, 19],
  edgeFinish₂ := ![4, 8, 3],
  mix := ![0, 200, 800],
  index := ![1, 4, 19],
  nonzeroWitness := ![15, 19, 4],
  B := 146296799 / 250000000
}

def coreAx3 : AxisCertificate := {
  edgeStart := ![3, 1, 13],
  edgeFinish := ![2, 4, 14],
  edgeStart₂ := ![2, 4, 14],
  edgeFinish₂ := ![1, 8, 15],
  mix := ![800, 800, 300],
  index := ![2, 4, 14],
  nonzeroWitness := ![9, 15, 1],
  B := 1372116187 / 1000000000
}

def coreAxes : Fin 4 → AxisCertificate
  | 0 => coreAx0
  | 1 => coreAx1
  | 2 => coreAx2
  | 3 => coreAx3

def c_core : ℚ := 5 / 1000
def r_min : ℚ := 51 / 10000

#eval (box.withCoreAxis (coreAxes 0) c_core r_min).variationRadiusSum 0 + 3 * variationError ≤ (coreAxes 0).B * box.δ
#eval (box.withCoreAxis (coreAxes 1) c_core r_min).variationRadiusSum 0 + 3 * variationError ≤ (coreAxes 1).B * box.δ
#eval (box.withCoreAxis (coreAxes 2) c_core r_min).variationRadiusSum 0 + 3 * variationError ≤ (coreAxes 2).B * box.δ
#eval (box.withCoreAxis (coreAxes 3) c_core r_min).variationRadiusSum 0 + 3 * variationError ≤ (coreAxes 3).B * box.δ

-- Check support upper
#eval ∀ i k, (box.withCoreAxis (coreAxes 0) c_core r_min).supportUpper 0 i k ≤ 0
#eval ∀ i k, (box.withCoreAxis (coreAxes 1) c_core r_min).supportUpper 0 i k ≤ 0
#eval ∀ i k, (box.withCoreAxis (coreAxes 2) c_core r_min).supportUpper 0 i k ≤ 0
#eval ∀ i k, (box.withCoreAxis (coreAxes 3) c_core r_min).supportUpper 0 i k ≤ 0

-- Check nonzero direction
#eval ∀ i, (box.withCoreAxis (coreAxes 0) c_core r_min).supportUpper 0 i ((coreAxes 0).nonzeroWitness i) < 0
#eval ∀ i, (box.withCoreAxis (coreAxes 1) c_core r_min).supportUpper 0 i ((coreAxes 1).nonzeroWitness i) < 0
#eval ∀ i, (box.withCoreAxis (coreAxes 2) c_core r_min).supportUpper 0 i ((coreAxes 2).nonzeroWitness i) < 0
#eval ∀ i, (box.withCoreAxis (coreAxes 3) c_core r_min).supportUpper 0 i ((coreAxes 3).nonzeroWitness i) < 0

-- Check weight budget and nonnegativity
#eval ∀ m : Fin 4, (box.withCoreAxis (coreAxes m) c_core r_min).weightBudget 0 ≤ (coreAxes m).B
#eval ∀ (m : Fin 4) i, 0 ≤ (box.withCoreAxis (coreAxes m) c_core r_min).weightLower 0 i
#eval ∀ m : Fin 4, ∃ i, 0 < (box.withCoreAxis (coreAxes m) c_core r_min).weightLower 0 i

-- Check core angle bound
#eval r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2

-- Check annular dominance
def D0 : ℚ := 118 / 1000000
def c_cone : ℚ := 17 / 1000
#eval ((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤ r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) * ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2)

