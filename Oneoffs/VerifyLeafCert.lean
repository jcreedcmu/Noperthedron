import Noperthedron.Nopert229.AtlasProjectiveGlobalCertificate

open Noperthedron.Nopert229
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveGlobalCertificate
open AtlasProjectiveLocalCertificate

def testBoxInterval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 0, φ := 0,
      x := 0,
      y := (-1 : ℚ) / 2048,
      z := (-1 : ℚ) / 768 }
    { θ := 0, φ := 0,
      x := (1 : ℚ) / 2048,
      y := 0,
      z := (-1 : ℚ) / 1024 }
    (by rw [AtlasPose.le_iff]; norm_num)

def testTriangle : AtlasProjectiveView.Triangle ℚ := ![
  ![(104895 : ℚ) / 167936, (2883 : ℚ) / 20992, (39977 : ℚ) / 167936],
  ![(13117 : ℚ) / 20992, (2883 : ℚ) / 20992, (39 : ℚ) / 164],
  ![(104905 : ℚ) / 167936, (23095 : ℚ) / 167936, (39 : ℚ) / 164]
]

def testCertificate : AxisCertificate where
  edgeStart := ![2, 10, 2]
  edgeFinish := ![1, 15, 1]
  edgeStart₂ := ![1, 15, 1]
  edgeFinish₂ := ![4, 19, 4]
  mix := ![0, 308, 1000]
  index := ![1, 15, 1]
  nonzeroWitness := ![15, 1, 10]
  B := (501315609 : ℚ) / 1000000000

def testBox : AtlasProjectiveGlobalCertificate.Box where
  interval := testBoxInterval
  root := 0
  triangle := testTriangle
  chart := 0
  certificate := testCertificate
  innerIndex := ![4, 15, 2]
  ballMultiplier := 0

theorem test_triangle_valid :
    AtlasProjectiveEdgeCertificate.SignedTriangleValid testBox.root testBox.triangle := by
  native_decide

theorem test_weights_valid :
    (∀ i, 0 ≤ testBox.weightLower i) ∧ (∃ i, 0 < testBox.weightLower i) := by
  native_decide

theorem test_directions_valid :
    ∀ i, testBox.supportUpper i (testBox.certificate.nonzeroWitness i) < 0 := by
  native_decide

theorem test_displacement_valid :
    testBox.displacementError ≤
      testBox.certifiedDisplacementLower - testBox.dBound * testBox.weightedDefectUpper := by
  native_decide

theorem test_box_valid_native : testBox.Valid := by
  native_decide

theorem test_box_valid_kernel : testBox.Valid := by
  decide +kernel

