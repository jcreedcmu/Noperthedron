import Noperthedron.Rupert.Basic

open scoped Matrix

/--
Affines α means α is a type that contains enough information to tell
us two affine transforms ℝ³ → ℝ³, the 'inner' and the 'outer'.
-/
class Affines (α : Type) where
  inner (pose : α) : ℝ³ →ᵃ[ℝ] ℝ³
  outer (pose : α) : ℝ³ →ᵃ[ℝ] ℝ³

/--
Shadows α means α is a type that contains enough information to tell
us two mappings ℝ³ → ℝ², the 'inner shadow' and the 'outer shadow'.
-/
class Shadows (α : Type) where
  inner (pose : α) (s : Set ℝ³) : Set ℝ²
  outer (pose : α) (s : Set ℝ³) : Set ℝ²

instance {α : Type} [Affines α] : Shadows α where
  inner x S := { proj_xy (Affines.inner x v) | v ∈ S }
  outer x S := { proj_xy (Affines.outer x v) | v ∈ S }

namespace Shadows

/--
A pose `p` demonstrates that a set `s` is rupert if the closure of the
`p`-inner-shadow of `s` is a subset of the interior of the
`p`-outer-shadow of `s`.
-/
def IsRupert {P : Type} [Shadows P] (p : P) (s : Set ℝ³) : Prop :=
  closure (Shadows.inner p s) ⊆ interior (Shadows.outer p s)

end Shadows
