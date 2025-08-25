import Rupert.Basic

open scoped Matrix

def snubCubeNumVerts : ℕ := 24
def snubCubeVerts : Fin snubCubeNumVerts → ℝ³ := sorry

/--
A finite collection of vertices in ℝ³
-/
structure Shape : Type where
  size : ℕ
  vertices : Fin size → ℝ³
