import Noperthedron.Basic
import Noperthedron.Util

/-
This file covers [SY25] §2.1.
-/

open scoped Matrix

namespace Nopert

open Real

def C1 : Fin 3 → ℚ := (1/259375205) * ![152024884, 0, 210152163]
def C2 : Fin 3 → ℚ := (1/10^10) * ![6632738028, 6106948881, 3980949609]
def C3 : Fin 3 → ℚ := (1/10^10) * ![8193990033, 5298215096, 1230614493]

noncomputable
def C1R : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => C1 i)

noncomputable
def C2R : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => C2 i)

noncomputable
def C3R : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => C3 i)

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

theorem c2_norm_bound : ‖C2R‖ ∈ Set.Ioo (98/100) (99/100) := by
  rw [EuclideanSpace.norm_eq]
  constructor
  · refine lt_sqrt_of_sq_lt ?_
    simp only [Real.norm_eq_abs, sq_abs]
    unfold C2R C2
    simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
    norm_num
  · refine (sqrt_lt' (by norm_num)).mpr ?_
    simp only [Real.norm_eq_abs, sq_abs]
    unfold C2R C2
    simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
    norm_num

theorem c3_norm_bound : ‖C3R‖ ∈ Set.Ioo (98/100) (99/100) := by
  rw [EuclideanSpace.norm_eq]
  constructor
  · refine lt_sqrt_of_sq_lt ?_
    simp only [Real.norm_eq_abs, sq_abs]
    unfold C3R C3
    simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
    norm_num
  · refine (sqrt_lt' (by norm_num)).mpr ?_
    simp only [Real.norm_eq_abs, sq_abs]
    unfold C3R C3
    simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
    norm_num

/-- This is half of the C30 defined in [SY25]. In order
to see that this is pointsymmetric, it's convenient to
do explicit pointsymmetrization later. -/
noncomputable
def C15 : List (ℝ³ →L[ℝ] ℝ³) := do
  let k ← List.range 15
  pure (RzL (2 * π * k / 15))

lemma length_c15 : C15.length = 15 := by simp [C15]

end Nopert

/--
The noperthedron, given as a finite list of vertices.
-/
noncomputable
def halfNopertVertList : List ℝ³ :=
    List.map (· Nopert.C1R) Nopert.C15 ++
    List.map (· Nopert.C2R) Nopert.C15 ++
    List.map (· Nopert.C3R) Nopert.C15

def pointsymmetrize (ℓ : List ℝ³) : List ℝ³ := ℓ ++ ℓ.map (fun x => -x)

noncomputable
def nopertVertList : List ℝ³ :=
  pointsymmetrize halfNopertVertList

def nopertNumVerts : ℕ := 90

lemma nopert_vert_list_length : nopertVertList.length = nopertNumVerts := by
  unfold nopertVertList
  simp only [List.length_append, List.length_map, pointsymmetrize]
  rfl

/--
The noperthedron, given as a finite set of vertices.
-/
noncomputable
def nopertVerts : Fin nopertVertList.length → ℝ³ := nopertVertList.get

/--
The noperthedron, given as a set of vertices.
-/
noncomputable
def nopertVertSet : Set ℝ³ := Set.range nopertVerts

/--
The noperthedron, given as a manifestly finite set of vertices.
-/
noncomputable
def nopertVertFinset : Finset ℝ³ := nopertVertList.toFinset

instance : Nonempty nopertVertFinset := by
  refine Finset.Nonempty.to_subtype ?_
  unfold nopertVertFinset
  simp only [List.toFinset_nonempty_iff]
  refine List.ne_nil_of_length_pos ?_
  rw [nopert_vert_list_length, nopertNumVerts]
  norm_num

noncomputable
def nopert : Shape where
  size := nopertNumVerts
  vertices := nopertVerts

lemma pointsymmetrization_is_pointsym (ℓ : List ℝ³) :
    PointSym { x | x ∈ pointsymmetrize ℓ } := by
  intro a ha
  refine List.mem_append.mpr ?_
  cases List.mem_append.mp ha with
  | inl ha => exact Or.inr (List.mem_map_of_mem ha)
  | inr ha =>
    refine Or.inl ?_
    have ⟨c, hc, e⟩ := List.exists_of_mem_map ha
    rw [← e]
    simp only [neg_neg]
    exact hc

theorem nopert_verts_pointsym : PointSym nopertVertSet := by
  rw [nopertVertSet, nopertVerts, Set.range_list_get]
  simp only [nopertVertList]
  apply pointsymmetrization_is_pointsym

/--
The noperthedron is pointsymmetric.
-/
theorem nopert_point_symmetric : PointSym nopert.hull := by
  exact hull_pres_pointsym nopert_verts_pointsym
