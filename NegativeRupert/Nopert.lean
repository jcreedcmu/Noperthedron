import NegativeRupert.Basic
import NegativeRupert.MatrixCand
import NegativeRupert.ViewCand

def nopertNumVerts : ℕ := 24 -- TODO: this is wrong
def nopertVerts : Fin nopertNumVerts → ℝ³ := sorry

def nopert : Shape where
  size := nopertNumVerts
  vertices := nopertVerts
