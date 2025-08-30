import NegativeRupert.Basic
import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand

def nopertCubeNumVerts : ℕ := 24
def nopertCubeVerts : Fin nopertCubeNumVerts → ℝ³ := sorry

def nopertCube : Shape := sorry

def nopertCand (mp : MatrixPose) : MatrixCand :=
  { pose := mp
    shape := nopertCube }

def nopertViewCand (vp : ViewPose) : ViewCand :=
  { pose := vp
    shape := nopertCube }
