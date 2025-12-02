import Noperthedron.Rupert.Basic
import Noperthedron.Basic

open scoped Matrix

/--
PoseLike α means α is a type that contains enough information to tell
us two affine transforms ℝ³ → ℝ³, the 'inner' and the 'outer'.
-/
class PoseLike (α : Type) where
  inner (pose : α) : ℝ³ →ᵃ[ℝ] ℝ³
  outer (pose : α) : ℝ³ →ᵃ[ℝ] ℝ³

def innerShadow {α : Type} [PoseLike α] (pose : α) (S : Set ℝ³) : Set ℝ² :=
  { proj_xyL (PoseLike.inner pose v) | v ∈ S }

def outerShadow {α : Type} [PoseLike α] (pose : α) (S : Set ℝ³) : Set ℝ² :=
  { proj_xyL (PoseLike.outer pose v) | v ∈ S }

/--
A pose `p` demonstrates that a set `s` is rupert if the closure of the
`p`-inner-shadow of `s` is a subset of the interior of the
`p`-outer-shadow of `s`.
-/
def RupertPose {P : Type} [PoseLike P] (p : P) (s : Set ℝ³) : Prop :=
  closure (innerShadow p s) ⊆ interior (outerShadow p s)

noncomputable
def innerProj {P : Type} [PoseLike P] (pose : P) : ℝ³ →ᵃ[ℝ] ℝ² :=
  proj_xyL.toAffineMap ∘ᵃ PoseLike.inner pose

noncomputable
def outerProj {P : Type} [PoseLike P] (pose : P) : ℝ³ →ᵃ[ℝ] ℝ² :=
  proj_xyL.toAffineMap ∘ᵃ PoseLike.outer pose
