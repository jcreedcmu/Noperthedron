import NegativeRupert.Basic
import NegativeRupert.Util

open scoped Matrix

namespace Nopert

open Real

/-
These constants are taken from [SY25] §2.
-/
def C1 : Fin 3 → ℚ := (1/259375205) * ![152024884, 0, 210152163]
def C2 : Fin 3 → ℚ := (1/10^10) * ![6632738028, 6106948881, 3980949609]
def C3 : Fin 3 → ℚ := (1/10^10) * ![8193990033, 5298215096, 1230614493]

noncomputable
def C1R : EuclideanSpace ℝ (Fin 3) := fun i => C1 i

noncomputable
def C2R : EuclideanSpace ℝ (Fin 3) := fun i => C2 i

noncomputable
def C3R : EuclideanSpace ℝ (Fin 3) := fun i => C3 i

theorem c1_norm_one : ‖C1R‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have lez : 0 ≤ ∑ i, ‖C1R i‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact sq_nonneg (‖C1R i‖)
  rw [← Real.sq_sqrt lez]
  simp only [Real.norm_eq_abs, sq_abs]
  unfold C1R C1
  simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
  norm_num

/- TODO(easy) -/
theorem c2_norm_bound : ‖C2‖ ∈ Set.Ioo (98/100) (99/100) := by
  sorry

/- TODO(easy) -/
theorem c3_norm_bound : ‖C3‖ ∈ Set.Ioo (98/100) (99/100) := by
  sorry

-- rotation about z-axis by θ
noncomputable
def Rz (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0;
     sin θ,  cos θ, 0;
     0,      0,     1]

noncomputable
def C30 : List (Matrix (Fin 3) (Fin 3) ℝ) := do
  let k ← List.range 15
  let ℓ ← List.range 2
  pure ((-1)^ℓ * (Rz (2 * π * k / 15)))

lemma length_c30 : C30.length = 30 := by simp [C30]

end Nopert

/--
The noperthedron, given as a finite list of vertices.
-/
noncomputable
def nopertVertList : List ℝ³ :=
    List.map (· *ᵥ Nopert.C1R) Nopert.C30 ++
    List.map (· *ᵥ Nopert.C2R) Nopert.C30 ++
    List.map (· *ᵥ Nopert.C3R) Nopert.C30

def nopertNumVerts : ℕ := 90

lemma nopert_vert_list_length : nopertVertList.length = nopertNumVerts := by
  unfold nopertVertList
  simp only [List.length_append, List.length_map, Nopert.length_c30]
  rfl

/--
The noperthedron, given as a finite set of vertices.
-/
noncomputable
def nopertVerts (i : Fin nopertNumVerts) : ℝ³ := by
  rw [← nopert_vert_list_length] at i
  exact nopertVertList.get i

noncomputable
def nopert : Shape where
  size := nopertNumVerts
  vertices := nopertVerts

/- TODO(medium) -/
theorem nopert_point_symmetric : PointSym nopert.hull := by
  sorry
