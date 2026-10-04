module

public import Noperthedron.Atlas.ProjectiveView

@[expose] public section


/-!
# min3 / max3

Three-way minima and maxima over rationals, with their basic bounds.

(Extracted, with only what the certificates use, from the earlier snub-cube
proof attempt.)
-/

namespace Noperthedron.Atlas.ProjectiveEdgeCertificate

open scoped RealInnerProductSpace
open Noperthedron.Checker
open Noperthedron.BalancedSupport
open CayleyEdgeCertificate
open ProjectiveView

def max3 (f : Fin 3 → ℚ) : ℚ := max (f 0) (max (f 1) (f 2))
def min3 (f : Fin 3 → ℚ) : ℚ := min (f 0) (min (f 1) (f 2))

theorem le_max3 (f : Fin 3 → ℚ) (i : Fin 3) : f i ≤ max3 f := by
  fin_cases i <;> simp [max3]

theorem min3_le (f : Fin 3 → ℚ) (i : Fin 3) : min3 f ≤ f i := by
  fin_cases i <;> simp [min3]

end Noperthedron.Atlas.ProjectiveEdgeCertificate

end
