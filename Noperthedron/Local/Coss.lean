import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Bounding
import Noperthedron.Local.Prelims

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 33 -/
theorem coss {δ ε θ θ_ φ φ_ : ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    let M := rotM θ φ
    let M_ := rotM θ_ φ_
    (⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
     ((‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε))
    ≤
     ⟪M P, M (P - Q)⟫ / (‖M P‖ * ‖M (P - Q)‖):= by
  sorry
