import Noperthedron.Basic
import Noperthedron.RationalApprox.Basic
import Noperthedron.Local.EpsSpanning

namespace RationalApprox

open scoped RealInnerProductSpace Real
open scoped Matrix


/-- [SY25] Definition 45. Note that the "+ 1" at the type Fin 3 wraps.
  We don't include in this definition the constraint that θ, φ ∈ [-4, 4] or
  that ‖P₁‖, ‖P₂‖, ‖P₃‖ ≤ 1 + κ.
  If a user of this code wants to impose those, they'll have to separately. -/
/- QUESTION: should be we be casting to ℝ to take the inner product?;
   on the one hand, we don't *have* to, because rotR (π / 2) is a valid 90° rotation on rationals.
   And should ε be real or rational? -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℚ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) + 6 * κ <
      ⟪rotR (π / 2) (↑(rotMℚ θ φ (P i)) : ℝ²), (↑(rotMℚ θ φ (P (i + 1))) : ℝ²)⟫

def κApproxTri (A : Local.Triangle) (A' : RationalApprox.Triangle) : Prop :=
  ∀ i, ‖A i - (↑(A' i) : ℝ³)‖ ≤ κ

/- [SY25 Lemma 46] -/
theorem ek_spanning_imp_e_spanning (P : Local.Triangle) (P' : RationalApprox.Triangle)
    (hk : κApproxTri P P') (θ φ ε : ℚ) (hspan : P'.Spanning θ φ ε) : P.Spanning θ φ ε := by
  sorry
