import Noperthedron.Local
import Noperthedron.RationalApprox

namespace RationalApprox

notation "ℚ³" => EuclideanSpace ℚ (Fin 3)
def RationalTriangle : Type := Fin 3 → ℚ³

instance : Coe ℚ³ ℝ³ where
  coe qv := WithLp.toLp 2 (qv ·)

def κApproxTri (A : Local.Triangle) (A' : RationalTriangle) : Prop :=
  ∀ i, ‖A i - A' i‖ ≤ κ

theorem rational_local : False := by
  sorry
