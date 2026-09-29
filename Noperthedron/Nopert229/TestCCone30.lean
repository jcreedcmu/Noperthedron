import Noperthedron.Nopert229.TestFlockTheorem
import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open Noperthedron.SnubCube
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveLocalCertificate
open AtlasProjectiveView

def box260 : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := 1 / 1000
  δ := 260 / 1000000
  r := 4 / 100000

def c_cone : ℚ := 25 / 1000

#eval decide (box260.decomposedBarycentricValid (25 / 1000))
#eval decide (box260.decomposedBarycentricValid (251 / 10000))
#eval decide (box260.decomposedBarycentricValid (252 / 10000))
#eval decide (box260.decomposedBarycentricValid (255 / 10000))
#eval decide (box260.decomposedBarycentricValid (26 / 1000))

theorem test_margin : box260.δ ≤ c_cone := by decide +kernel
theorem test_annular :
    ((1 / 2 : ℚ) * box260.r ^ 2 * (box260.certificate 0).B + D0) ^ 2 ≤
      r_min ^ 2 * (1 - (1 / 4 : ℚ) * box260.r ^ 2) *
        ((c_cone - box260.δ) ^ 2 * (box260.certificate 0).B ^ 2) := by decide +kernel
theorem test_comp_angle : box260.r ^ 2 * (1 + (box260.c - box260.δ) ^ 2) ≤ 4 * (box260.c - box260.δ) ^ 2 := by decide +kernel

