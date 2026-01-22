import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.Local.Prelims

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- The intersection of the δ-disc centered at Q with the interior of the convex hull of P -/
def sect (δ : ℝ) (Q : Euc(2)) (P : Finset Euc(2)) : Set Euc(2) :=
  Metric.ball Q δ ∩ interior (convexHull ℝ P)

/--
[SY25] Definition 31
"Q is δ-locally maximally distant with respect to Q_" or "Q is δ-LMD(Q_)".
-/
def LocallyMaximallyDistant (δ : ℝ) (Q Q_ : Euc(2)) (P : Finset Euc(2)) : Prop :=
  ∀ A ∈ sect δ Q_ P, ‖A‖ < ‖Q‖

/--
[SY25] Lemma 32
-/
theorem inner_ge_implies_LMD {P : Finset Euc(2)} {Q Q_ : Euc(2)} {δ r : ℝ}
    (hQ : Q ∈ P) (hQ_ : ‖Q - Q_‖ < δ) (hr : 0 < r) (hrQ : r < ‖Q‖)
    (hle : ∀ Pᵢ ∈ P, Pᵢ ≠ Q → δ / r ≤ ⟪Q, Q - Pᵢ⟫ / (‖Q‖ * ‖Q - Pᵢ‖)) :
    LocallyMaximallyDistant δ Q Q_ P := by
  sorry
