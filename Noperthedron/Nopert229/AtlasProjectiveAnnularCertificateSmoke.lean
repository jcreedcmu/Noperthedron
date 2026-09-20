module

public import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
public meta import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
public import Noperthedron.Nopert229.AtlasProjectiveLocalRigidity
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
open AtlasProjectiveLocalCertificate AtlasProjectiveView AtlasProjectiveLocalRigidity
open BalancedSupport
open scoped RealInnerProductSpace

set_option linter.unusedVariables false

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

/-- Concrete instance of the 9-vertex hull inner core certificate for cell `031213002112122012121`.
Idea 3 from TINY_SLIVER.md: contacts at vertices v₂, v₄, v₁₅ on the true 9-vertex hull.
Because all 3 contacts lie on the true 9-vertex hull, their support upper bounds are strictly ≤ 0. -/
def cert_hull : AxisCertificate := {
  edgeStart := ![3, 1, 10]
  edgeFinish := ![2, 4, 15]
  edgeStart₂ := ![2, 4, 15]
  edgeFinish₂ := ![1, 8, 19]
  mix := ![800, 800, 800]
  index := ![2, 4, 15]
  nonzeroWitness := ![9, 15, 1]
  B := 18061 / 10000
}

def box_core : Box where
  interval := interval
  root := 0
  triangle := triangle
  chart := 0
  symmetryIndex := 0
  certificate := fun _ => cert_hull
  c := 2133147 / 1000000000
  δ := 333 / 1000000000
  r := 1 / 1000

theorem hB_pos_core : ∀ (j : Fin 4), 0 < (box_core.certificate j).B := by decide +kernel
theorem hsupport_zero_core : ∀ (j : Fin 4) (i : Fin 3) (k : VertexIndex), box_core.supportUpper j i k ≤ 0 := by decide +kernel
theorem hdir_nonzero_core : ∀ (j : Fin 4) (i : Fin 3), box_core.supportUpper j i ((box_core.certificate j).nonzeroWitness i) < 0 := by decide +kernel
theorem hweight_nonneg_core : ∀ (j : Fin 4) (i : Fin 3), 0 ≤ box_core.weightLower j i := by decide +kernel
theorem hweight_pos_core : ∀ (j : Fin 4), ∃ i, 0 < box_core.weightLower j i := by decide +kernel

def cert_core : InnerCoreCertificate where
  innerIndex := ![2, 4, 15]
  cert := cert_hull

/-- Sibling Axis 1 from node `031213002112122012120`. -/
def cert1 : AxisCertificate := {
  edgeStart := ![15, 2, 8]
  edgeFinish := ![19, 1, 9]
  edgeStart₂ := ![19, 1, 9]
  edgeFinish₂ := ![3, 4, 10]
  mix := ![200, 200, 200]
  index := ![19, 1, 9]
  nonzeroWitness := ![8, 15, 2]
  B := 898481993 / 1000000000
}

/-- Sibling Axis 2 from node `031213002112122012120`. -/
def cert2 : AxisCertificate := {
  edgeStart := ![2, 10, 10]
  edgeFinish := ![1, 15, 15]
  edgeStart₂ := ![1, 15, 15]
  edgeFinish₂ := ![4, 19, 19]
  mix := ![0, 333, 0]
  index := ![1, 15, 15]
  nonzeroWitness := ![15, 1, 4]
  B := 254450361 / 500000000
}

/-- Sibling Axis 3 from node `031213002112122012120`. -/
def cert3 : AxisCertificate := {
  edgeStart := ![3, 4, 14]
  edgeFinish := ![2, 8, 15]
  edgeStart₂ := ![2, 8, 15]
  edgeFinish₂ := ![1, 9, 19]
  mix := ![800, 800, 800]
  index := ![2, 8, 15]
  nonzeroWitness := ![9, 19, 1]
  B := 264825469 / 200000000
}

def box_sib (cert : AxisCertificate) : Box where
  interval := interval
  root := 0
  triangle := triangle
  chart := 0
  symmetryIndex := 0
  certificate := fun _ => cert
  c := 2133147 / 1000000000
  δ := 333 / 1000000000
  r := 1 / 1000

theorem hB_pos_cert1 : ∀ (j : Fin 4), 0 < ((box_sib cert1).certificate j).B := by decide +kernel
theorem hsupport_cert1 : ∀ (j : Fin 4) (i : Fin 3) (k : VertexIndex), (box_sib cert1).supportUpper j i k ≤ 0 := by decide +kernel
theorem hdir_nonzero_cert1 : ∀ (j : Fin 4) (i : Fin 3), (box_sib cert1).supportUpper j i (((box_sib cert1).certificate j).nonzeroWitness i) < 0 := by decide +kernel
theorem hweight_nonneg_cert1 : ∀ (j : Fin 4) (i : Fin 3), 0 ≤ (box_sib cert1).weightLower j i := by decide +kernel
theorem hweight_pos_cert1 : ∀ (j : Fin 4), ∃ i, 0 < (box_sib cert1).weightLower j i := by decide +kernel

theorem hB_pos_cert2 : ∀ (j : Fin 4), 0 < ((box_sib cert2).certificate j).B := by decide +kernel
theorem hsupport_cert2 : ∀ (j : Fin 4) (i : Fin 3) (k : VertexIndex), (box_sib cert2).supportUpper j i k ≤ 0 := by decide +kernel
theorem hdir_nonzero_cert2 : ∀ (j : Fin 4) (i : Fin 3), (box_sib cert2).supportUpper j i (((box_sib cert2).certificate j).nonzeroWitness i) < 0 := by decide +kernel
theorem hweight_nonneg_cert2 : ∀ (j : Fin 4) (i : Fin 3), 0 ≤ (box_sib cert2).weightLower j i := by decide +kernel
theorem hweight_pos_cert2 : ∀ (j : Fin 4), ∃ i, 0 < (box_sib cert2).weightLower j i := by decide +kernel

theorem hB_pos_cert3 : ∀ (j : Fin 4), 0 < ((box_sib cert3).certificate j).B := by decide +kernel
theorem hsupport_cert3 : ∀ (j : Fin 4) (i : Fin 3) (k : VertexIndex), (box_sib cert3).supportUpper j i k ≤ 0 := by decide +kernel
theorem hdir_nonzero_cert3 : ∀ (j : Fin 4) (i : Fin 3), (box_sib cert3).supportUpper j i (((box_sib cert3).certificate j).nonzeroWitness i) < 0 := by decide +kernel
theorem hweight_nonneg_cert3 : ∀ (j : Fin 4) (i : Fin 3), 0 ≤ (box_sib cert3).weightLower j i := by decide +kernel
theorem hweight_pos_cert3 : ∀ (j : Fin 4), ∃ i, 0 < (box_sib cert3).weightLower j i := by decide +kernel

/-- Ruling out adversary poses in the inner core `‖Q - 1‖ ≤ r_min` along the
exceptional cone for cell `031213002112122012121` using `cert_hull`.
The support defect premise is discharged unconditionally by `hsupport_zero_core`. -/
theorem not_rupertPose_cell_inner_core
    (hdisplacement : ∀ {p : AtlasPose ℝ} (hp : p ∈ box_core.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box_core.root p →
      InTriangle (toReal box_core.triangle) (AtlasProjectiveView.normalizedView box_core.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box_core.chart offset) box_core.symmetryIndex)),
        ‖Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box_core.chart offset) box_core.symmetryIndex) - 1‖ ≤ (r_min : ℝ) →
        exceptional a.signedAxis →
        0 ≤ ∑ i, (box_core.certificate 0).exactWeight box_core p i *
          ⟪direction box_core.root p ((box_core.certificate 0).exactEdge i),
            proj_xyL ((p.matrixPoseWithOffset box_core.chart offset).innerRot.val.toEuclideanLin
              (exactPolyhedron.v (symmetryAction box_core.symmetryIndex (cert_core.innerIndex i)))) -
            proj_xyL ((p.matrixPoseWithOffset box_core.chart offset).outerRot.val.toEuclideanLin
              (exactPolyhedron.v (symmetryAction box_core.symmetryIndex (cert_core.cert.index i))))⟫) :
    ∀ {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
        ‖Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ ≤ (r_min : ℝ) →
        exceptional a.signedAxis →
        ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  intro p hp offset hscale hmem a hr hexc
  exact not_rupertPose_of_inner_core_certificate box_core cert_core r_min exceptional
    rfl hdir_nonzero_core hweight_nonneg_core hweight_pos_core hsupport_zero_core
    hdisplacement hp offset hscale hmem a hr hexc

/-- High-level identity tube property for cell `031213002112122012121`:
Any pose in this cell has NO Rupert passage for any planar translation,
composed from:
1. Annular exceptional cone (`not_rupertPose_cell_exceptional_annulus`),
2. Non-exceptional complementary directions (`h_complement`), and
3. Inner exceptional core (`not_rupertPose_cell_inner_core`). -/
theorem not_rupertPose_cell_composed
    (h_complement : ∀ {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
        ¬ exceptional a.signedAxis →
        ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull)
    (hdisplacement : ∀ {p : AtlasPose ℝ} (hp : p ∈ box_core.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box_core.root p →
      InTriangle (toReal box_core.triangle) (AtlasProjectiveView.normalizedView box_core.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box_core.chart offset) box_core.symmetryIndex)),
        ‖Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box_core.chart offset) box_core.symmetryIndex) - 1‖ ≤ (r_min : ℝ) →
        exceptional a.signedAxis →
        0 ≤ ∑ i, (box_core.certificate 0).exactWeight box_core p i *
          ⟪direction box_core.root p ((box_core.certificate 0).exactEdge i),
            proj_xyL ((p.matrixPoseWithOffset box_core.chart offset).innerRot.val.toEuclideanLin
              (exactPolyhedron.v (symmetryAction box_core.symmetryIndex (cert_core.innerIndex i)))) -
            proj_xyL ((p.matrixPoseWithOffset box_core.chart offset).outerRot.val.toEuclideanLin
              (exactPolyhedron.v (symmetryAction box_core.symmetryIndex (cert_core.cert.index i))))⟫) :
    ∀ {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p) →
      ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  apply valid_imp_not_translated_rupert_of_three_way_split box r_min exceptional
  · intro p hp offset hscale hmem a hr hexc
    exact not_rupertPose_cell_exceptional_annulus hp offset hscale hmem a hr hexc
  · exact h_complement
  · intro p hp offset hscale hmem a hr hexc
    exact not_rupertPose_cell_inner_core hdisplacement hp offset hscale hmem a hr hexc

end Noperthedron.Nopert229.AtlasProjectiveAnnularCertificateSmoke
end
