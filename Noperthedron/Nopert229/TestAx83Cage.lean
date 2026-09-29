import Noperthedron.Nopert229.TestFlockTheorem
import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open Noperthedron.SnubCube
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveLocalCertificate
open AtlasProjectiveView

def ax83 : AxisCertificate := {
  edgeStart := ![2, 8, 3],
  edgeFinish := ![1, 9, 2],
  edgeStart₂ := ![1, 9, 2],
  edgeFinish₂ := ![4, 10, 1],
  mix := ![0, 0, 1000],
  index := ![1, 9, 2],
  nonzeroWitness := ![15, 2, 9],
  B := 264412343/200000000
}

-- Try cage with ax83 and complement axes ax2, ax1, ax3 (swapped 1 and 2 to make det positive)
def box83 : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := fun | 0 => ax83 | 1 => ax2 | 2 => ax1 | 3 => ax3
  c := 1 / 1000
  δ := 260 / 1000000
  r := 4 / 100000

def c_cone : ℚ := 25 / 1000

#eval box83.decomposedBarycentricValid c_cone
