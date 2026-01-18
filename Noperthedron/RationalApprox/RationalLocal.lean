import Noperthedron.Local
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.EpsKapSpanning

namespace RationalApprox

def κApproxTri (A : Local.Triangle) (A' : RationalApprox.Triangle) : Prop :=
  ∀ i, ‖A i - (↑(A' i) : ℝ³)‖ ≤ κ

theorem rational_local : False := by
  sorry
