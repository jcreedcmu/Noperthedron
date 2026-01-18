import Noperthedron.Basic
import Noperthedron.RationalApprox.Basic


namespace RationalApprox

open scoped RealInnerProductSpace Real
open scoped Matrix


/-- [SY25] Definition 45. Note that the "+ 1" at the type Fin 3 wraps.
  We don't include in this definition the constraint that θ, φ ∈ [-4, 4] or
  that ‖P₁‖, ‖P₂‖, ‖P₃‖ ≤ 1 + κ.
  If a user of this code wants to impose those, they'll have to separately. -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℚ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) + 6 * κ <
      ⟪rotR (π / 2) (↑(rotMℚ θ φ (P i)) : ℝ²), (↑(rotMℚ  θ φ (P (i + 1))) : ℝ²)⟫
