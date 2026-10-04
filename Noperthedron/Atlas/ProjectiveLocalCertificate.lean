module

public import Noperthedron.Checker.RatQuadratic3
public import Noperthedron.Checker.SqrtFixed
public import Noperthedron.Atlas.ProjectiveEdgeCertificate

@[expose] public section


/-!
# Rational vectors and linear forms on view triangles

`VectorQ`, `mulLinear` and coordinate bounds for linear forms evaluated over
projective view triangles.

(Extracted, with only what the certificates use, from the earlier snub-cube
proof attempt.)
-/

namespace Noperthedron.Atlas.ProjectiveLocalCertificate

open scoped RealInnerProductSpace
open Noperthedron.Checker
open Noperthedron.BalancedSupport
open CayleyEdgeCertificate ProjectiveView ProjectiveEdgeCertificate

abbrev VectorQ := Fin 3 → ℚ

/-- Product of two homogeneous linear forms. -/
def mulLinear (a b : VectorQ) : RatQuadratic3 :=
  { c0 := 0, cx := 0, cy := 0, cz := 0,
    cxx := a 0 * b 0,
    cxy := a 0 * b 1 + a 1 * b 0,
    cxz := a 0 * b 2 + a 2 * b 0,
    cyy := a 1 * b 1,
    cyz := a 1 * b 2 + a 2 * b 1,
    czz := a 2 * b 2 }

theorem evalReal_mulLinear (a b : VectorQ) (n : Fin 3 → ℝ) :
    (mulLinear a b).evalReal (n 0) (n 1) (n 2) =
      linearValue n (fun c => (a c : ℝ)) *
        linearValue n (fun c => (b c : ℝ)) := by
  simp [mulLinear, RatQuadratic3.evalReal, linearValue]
  ring

def unitCoordinate (coordinate : Fin 3) : Fin 3 → ℝ :=
  fun c => if c = coordinate then 1 else 0

@[simp] theorem linearValue_unitCoordinate (n : Fin 3 → ℝ)
    (coordinate : Fin 3) :
    linearValue n (unitCoordinate coordinate) = n coordinate := by
  fin_cases coordinate <;> simp [linearValue, unitCoordinate]

theorem coordinate_mem_triangleBounds {triangle : Triangle ℚ}
    {n : Fin 3 → ℝ} (hmem : InTriangle (toReal triangle) n)
    (coordinate : Fin 3) :
    n coordinate ∈ Set.Icc
      ((min3 (fun j => triangle j coordinate) : ℚ) : ℝ)
      ((max3 (fun j => triangle j coordinate) : ℚ) : ℝ) := by
  constructor
  · rw [← linearValue_unitCoordinate n coordinate]
    apply le_linearValue_of_mem hmem
    intro j
    have hmin := min3_le (fun j => triangle j coordinate) j
    rw [linearValue_unitCoordinate]
    change ((min3 (fun j => triangle j coordinate) : ℚ) : ℝ) ≤
      (triangle j coordinate : ℝ)
    exact_mod_cast hmin
  · rw [← linearValue_unitCoordinate n coordinate]
    apply linearValue_le_of_mem hmem
    intro j
    have hmax := le_max3 (fun j => triangle j coordinate) j
    rw [linearValue_unitCoordinate]
    change (triangle j coordinate : ℝ) ≤
      ((max3 (fun j => triangle j coordinate) : ℚ) : ℝ)
    exact_mod_cast hmax

theorem norm_le_sum_abs_coordinates (v : ℝ³) :
    ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2),
      sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]

theorem norm_quarterTurn (u : ℝ²) : ‖quarterTurn u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [quarterTurn, Fin.sum_univ_two, sq_abs]
  ring

end Noperthedron.Atlas.ProjectiveLocalCertificate

end
