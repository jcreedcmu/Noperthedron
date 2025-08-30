import Rupert.Basic

open scoped Matrix

/--
A finite collection of vertices in ℝ³
-/
structure Shape : Type where
  size : ℕ
  vertices : Fin size → ℝ³

namespace Shape

def hull (s : Shape) : Set ℝ³ := convexHull ℝ (Set.range s.vertices)

end Shape
