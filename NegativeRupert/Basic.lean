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

/- FIXME: Is there not a better way to name the standard euclidean basis?
This seems pretty verbose. -/
noncomputable
def e3 : Module.Basis (Fin 3) ℝ ℝ³ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

noncomputable
def rotR (α : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ :=
  let A : Matrix (Fin 3) (Fin 3) ℝ := sorry
  (A.toLin e3 e3).toAffineMap

noncomputable
def rotM (θ : ℝ) (φ : ℝ) : ℝ³ →ᵃ[ℝ] ℝ³ :=
  let A : Matrix (Fin 3) (Fin 3) ℝ := sorry
  (A.toLin e3 e3).toAffineMap
