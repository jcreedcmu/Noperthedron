import NegativeRupert.Basic
import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand

def snubCubeNumVerts : ℕ := 24
def snubCubeVerts : Fin snubCubeNumVerts → ℝ³ := sorry

def snubCube : Shape := sorry

def snubCand (mp : MatrixPose) : MatrixCand :=
  { pose := mp
    shape := snubCube }

def snubViewCand (vp : ViewPose) : ViewCand :=
  { pose := vp
    shape := snubCube }
