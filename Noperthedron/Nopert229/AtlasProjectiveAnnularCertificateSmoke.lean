module

public import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
public meta import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
public import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
public import Noperthedron.BalancedSupport.Rodrigues

@[expose] public section

/-!
# Executable verification of an annular exceptional-cone certificate on a concrete cell

We instantiate `not_rupertPose_of_annular_exceptional_cone_certificate` on the real
depth-21 sliver cell `031213002112122012121` using the concrete rational certificate
data from `tree_0.json`.
-/

namespace Noperthedron.Nopert229.AtlasProjectiveAnnularCertificateSmoke

open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveLocalCertificate AtlasProjectiveView
open BalancedSupport

def interval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 0, φ := 0
      x := -1 / 1000000, y := -1 / 1000000, z := -1 / 1000000 }
    { θ := 0, φ := 0
      x := 1 / 1000000, y := 1 / 1000000, z := 1 / 1000000 }
    (by rw [AtlasPose.le_iff]; norm_num)

/-- The exact projective view triangle for cell `031213002112122012121`. -/
def triangle : AtlasProjectiveView.Triangle ℚ := ![
  ![13439209 / 21495808, 11936767 / 85983232, 494869 / 2097152],
  ![26878413 / 42991616, 373023 / 2686976, 247435 / 1048576],
  ![53756867 / 85983232, 373023 / 2686976, 494869 / 2097152]
]

/-- The exact rational axis certificate from node `031213002112122012120`. -/
def cert0 : AxisCertificate :=
  { edgeStart := ![3, 1, 13]
    edgeFinish := ![2, 4, 14]
    edgeStart₂ := ![2, 4, 14]
    edgeFinish₂ := ![1, 8, 15]
    mix := ![800, 800, 200]
    index := ![2, 4, 14]
    nonzeroWitness := ![9, 15, 1]
    B := 139662011 / 100000000 }

def box : Box where
  interval := interval
  root := 0
  triangle := triangle
  chart := 0
  symmetryIndex := 0
  certificate := fun _ => cert0
  c := 2133147 / 1000000000
  δ := 333 / 1000000000
  r := 1 / 1000

/-- Contact 2 has a tiny positive silhouette defect of ~2.02e-6 on this cell. -/
def defectQ : ℚ := 202 / 100000000
def defect : Fin 4 → Fin 3 → ℚ := fun _ i =>
  if i = 2 then defectQ else 0

def D : Fin 4 → ℚ := fun _ => 8 / 10000000 -- 8e-7

def r_min : ℚ := 1 / 10000 -- 1e-4
def c_cone : ℚ := 99 / 100   -- cos(cone) = 0.99

theorem hB_pos : ∀ (j : Fin 4), 0 < (box.certificate j).B := by decide +kernel
theorem hdelta_nonneg : 0 ≤ box.δ := by norm_num [box]
theorem hD_nonneg : ∀ (j : Fin 4), 0 ≤ D j := by decide +kernel
theorem hdefect_nonneg : ∀ (j : Fin 4) (i : Fin 3), 0 ≤ defect j i := by decide +kernel
theorem hvariation : ∀ (j : Fin 4), box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ := by decide +kernel
theorem hsupport : ∀ (j : Fin 4) (i : Fin 3) (k : VertexIndex), box.supportUpper j i k ≤ defect j i := by decide +kernel
theorem hdir_nonzero : ∀ (j : Fin 4) (i : Fin 3), box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0 := by decide +kernel
theorem hbudget : ∀ (j : Fin 4), box.weightBudget j ≤ (box.certificate j).B := by decide +kernel
theorem hdefect_budget : ∀ (j : Fin 4), ∑ i, box.weightUpper j i * defect j i ≤ D j := by decide +kernel
theorem hweight_nonneg : ∀ (j : Fin 4) (i : Fin 3), 0 ≤ box.weightLower j i := by decide +kernel
theorem hweight_pos : ∀ (j : Fin 4), ∃ i, 0 < box.weightLower j i := by decide +kernel
theorem hmismatch : box.mismatchRadius ≤ box.r := by decide +kernel
theorem hannular_dominance :
  ((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D 0) ^ 2 ≤
    r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) *
      ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2) := by
  norm_num [box, D, r_min, c_cone, cert0]

def exceptional (axis : Euc(3)) : Prop :=
  (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0))

/-- Instantiated theorem for cell `031213002112122012121`:
Any adversary rotation in the annulus `r_min ≤ ‖Q - 1‖ ≤ r` whose signed axis
lies within the cone of aperture `cos θ = 0.99` around the certified axis 0
cannot produce a Rupert pose. -/
theorem not_rupertPose_cell_exceptional_annulus
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (offset : Euc(2))
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p))
    (a : AxisAngle ((relativeRotationAtSymmetry (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex).val.toEuclideanLin.toContinuousLinearMap))
    (hr_min : (r_min : ℝ) ≤ ‖(relativeRotationAtSymmetry (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex).val.toEuclideanLin.toContinuousLinearMap - 1‖)
    (hexc : exceptional a.signedAxis) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  have hexc_def : ∀ axis, exceptional axis ↔ (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0)) :=
    fun _ => Iff.rfl
  exact not_rupertPose_of_annular_exceptional_cone_certificate
    box 0 defect D r_min
    (by norm_num [r_min])
    (by norm_num [box])
    (by norm_num [box])
    hB_pos
    hdelta_nonneg
    hD_nonneg
    hdefect_nonneg
    hvariation
    hsupport
    hdir_nonzero
    hbudget
    hdefect_budget
    hweight_nonneg
    hweight_pos
    c_cone
    (by norm_num [c_cone, box])
    exceptional
    hexc_def
    hmismatch
    hannular_dominance
    hp offset hscale hmem a hr_min hexc

end Noperthedron.Nopert229.AtlasProjectiveAnnularCertificateSmoke
end
