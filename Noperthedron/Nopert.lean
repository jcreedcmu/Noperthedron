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
def C15 (pt : ℝ³) : Finset ℝ³ :=
  Finset.range 15 |> .image fun (k : ℕ)  =>
    RzL (2 * π * (k : ℝ) / 15) pt

lemma C15_nonempty (pt : ℝ³) : (C15 pt).Nonempty := by
  use (RzL 0 pt)
  have z : 0 ∈ Finset.range 15 := Finset.insert_eq_self.mp rfl
  simp only [C15, Finset.mem_image, Finset.mem_range]
  use 0
  simp only [Nat.ofNat_pos, CharP.cast_eq_zero, mul_zero, zero_div, and_self]

end Nopert

/--
Half of the vertices of the noperthedron
-/
noncomputable
def halfNopertVerts : Finset ℝ³ :=
    Nopert.C15 Nopert.C1R ∪
    Nopert.C15 Nopert.C2R ∪
    Nopert.C15 Nopert.C3R

lemma half_nopert_verts_nonempty : halfNopertVerts.Nonempty := by
  apply Finset.Nonempty.inl
  apply Finset.Nonempty.inl
  apply Nopert.C15_nonempty

noncomputable
def halfNopertNorms : Finset ℝ :=
  halfNopertVerts.image (‖·‖)

lemma half_nopert_norms_nonempty : halfNopertNorms.Nonempty := by
  simp only [halfNopertNorms, Finset.image_nonempty]
  exact half_nopert_verts_nonempty

lemma half_nopert_verts_norm_le_one : ∀ v ∈ halfNopertVerts, ‖v‖ ≤ 1 := by
  sorry

@[simp]
noncomputable
def pointsymmetrize (vs : Finset ℝ³) : Finset ℝ³ := vs ∪ vs.image (-·)

lemma pointsymmetrize_mem (vs : Finset ℝ³) (x : ℝ³)  :
    (x ∈ pointsymmetrize vs) ↔ (x ∈ vs ∨ -x ∈ vs) := by
  constructor
  · intro hx
    simp_all only [pointsymmetrize]
    let z :=  Finset.mem_union.mp hx
    simp only [Finset.mem_image] at z
    match z with
    | .inl h => left; assumption
    | .inr ⟨y, ⟨hy, hy'⟩⟩  => rw [← hy']; right; simpa
  · intro hq
    simp only [pointsymmetrize, Finset.mem_union, Finset.mem_image]
    match hq with
    | .inl h => left; exact h
    | .inr h => right; use -x; simpa

noncomputable
def nopertVerts : Finset ℝ³ :=
  pointsymmetrize halfNopertVerts

/--
The noperthedron, given as a set of vertices.
-/
noncomputable
def nopertVertSet : Set ℝ³ := nopertVerts

lemma nopert_verts_nonempty : nopertVerts.Nonempty := by
  simp only [nopertVerts]
  apply Finset.Nonempty.inl
  apply half_nopert_verts_nonempty

noncomputable
def nopert : Shape where
  vertices := nopertVerts

lemma pointsymmetrize_is_pointsym (vs : Finset ℝ³) :
    PointSym (pointsymmetrize vs : Set ℝ³) := by
  intro a ha
  simp only [SetLike.mem_coe]
  have z :  a ∈ vs ∨ -a ∈ vs :=  pointsymmetrize_mem vs a |>.mp ha
  have z' : -a ∈ vs ∨ -(-a) ∈ vs := cast (by rw [or_comm, neg_neg]) z
  exact pointsymmetrize_mem vs (-a) |>.mpr z'

theorem nopert_verts_pointsym : PointSym nopertVertSet :=
  pointsymmetrize_is_pointsym halfNopertVerts

/--
The noperthedron is pointsymmetric.
-/
theorem nopert_point_symmetric : PointSym nopert.hull := by
  exact hull_pres_pointsym nopert_verts_pointsym

/--
The point C1R is in the half-noperthedron
-/
lemma c1r_in_half_nopert_verts : Nopert.C1R ∈ halfNopertVerts := by
    simp only [halfNopertVerts]
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simp only [Nopert.C15, Finset.mem_image, Finset.mem_range]
    use 0
    simp

/--
The radius of the half-noperthedron is 1.
-/
theorem half_nopert_radius_one : polyhedron_radius halfNopertVerts half_nopert_verts_nonempty = 1 :=
  polyhedron_radius_def halfNopertVerts half_nopert_verts_nonempty
    Nopert.C1R c1r_in_half_nopert_verts Nopert.c1_norm_one half_nopert_verts_norm_le_one

/--
Pointsymmetrization preserves the radius of any set
-/
theorem pointsymmetrize_pres_radius {vs : Finset ℝ³} (vsne : vs.Nonempty) :
    polyhedron_radius (pointsymmetrize vs) (by simpa) = polyhedron_radius vs vsne := by
  sorry

/--
The radius of the noperthedron is 1.
-/
theorem Nopert.noperthedron_radius_one : polyhedron_radius nopertVerts nopert_verts_nonempty = 1 := by
  simp only [nopertVerts, pointsymmetrize_pres_radius half_nopert_verts_nonempty]
  exact half_nopert_radius_one
