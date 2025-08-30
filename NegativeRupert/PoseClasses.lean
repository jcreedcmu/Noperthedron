import Rupert.Basic

open scoped Matrix

class Affines (α : Type) where
  inner (pose : α) : ℝ³ →ᵃ[ℝ] ℝ³
  outer (pose : α) : ℝ³ →ᵃ[ℝ] ℝ³

class Shadows (α : Type) where
  inner (pose : α) (s : Set ℝ³) : Set ℝ²
  outer (pose : α) (s : Set ℝ³) : Set ℝ²

instance {α : Type} [Affines α] : Shadows α where
  inner x S := { proj_xy (Affines.inner x v) | v ∈ S }
  outer x S := { proj_xy (Affines.outer x v) | v ∈ S }

namespace Shadows

def IsRupert {P : Type} [Shadows P] (p : P) (s : Set ℝ³) : Prop :=
  closure (Shadows.inner p s) ⊆ interior (Shadows.outer p s)

def IsSafe {P : Type} [Shadows P] (p : P) (s : Set ℝ³) : Prop :=
  ∃ y, y ∈ Shadows.inner p s ∧ ¬ y ∈ Shadows.outer p s

end Shadows
