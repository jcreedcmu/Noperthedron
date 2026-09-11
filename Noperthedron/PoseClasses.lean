module

public import Noperthedron.Rupert.Basic
public import Noperthedron.Basic

@[expose] public section


open scoped Matrix

/--
PoseLike α means α is a type that contains enough information to tell
us two affine transforms ℝ³ → ℝ², the 'inner' and the 'outer' projections.
-/
class PoseLike (α : Type) where
  inner (pose : α) : ℝ³ →ᵃ[ℝ] ℝ²
  outer (pose : α) : ℝ³ →ᵃ[ℝ] ℝ²

def innerShadow {α : Type} [PoseLike α] (pose : α) (S : Set ℝ³) : Set ℝ² :=
  PoseLike.inner pose '' S

def outerShadow {α : Type} [PoseLike α] (pose : α) (S : Set ℝ³) : Set ℝ² :=
  PoseLike.outer pose '' S

/--
A pose `p` demonstrates that a set `s` is rupert if the closure of the
`p`-inner-shadow of `s` is a subset of the interior of the
`p`-outer-shadow of `s`.
-/
def RupertPose {P : Type} [PoseLike P] (p : P) (s : Set ℝ³) : Prop :=
  closure (innerShadow p s) ⊆ interior (outerShadow p s)

end
