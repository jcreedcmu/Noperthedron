import NegativeRupert.Basic

def nopertNumVerts : ℕ := 90

/--
The noperthedron, given as a finite set of vertices.

TODO(medium): See [SY25] §2 for the construction.
-/
def nopertVerts : Fin nopertNumVerts → ℝ³ := sorry

def nopert : Shape where
  size := nopertNumVerts
  vertices := nopertVerts
