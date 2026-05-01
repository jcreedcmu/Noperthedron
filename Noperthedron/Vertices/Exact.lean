import Noperthedron.Basic
import Noperthedron.Bounding
import Noperthedron.PointSym
import Noperthedron.Vertices.Index

/-!
This file covers [SY25] §2.1, defining the Noperthedron vertices.

## Main definitions

- `Noperthedron.exactVertex`: The exact Noperthedron vertices, as a function
  from `Noperthedron.VertexIndex` to `ℝ³`.

- `Noperthedron.exactPoly`: The vertices as a `GoodPoly`.

-/

open scoped Matrix

namespace Noperthedron

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
  have lez : 0 ≤ ∑ i, ‖C1R i‖ ^ 2 := by positivity
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

theorem c2_norm_le_one : ‖C2R‖ ≤ 1 := by
  grw [c2_norm_bound.2]
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

theorem c3_norm_le_one : ‖C3R‖ ≤ 1 := by
  grw [c3_norm_bound.2]
  norm_num

noncomputable
def Cpt : Fin 3 → ℝ³
| 0 => C1R
| 1 => C2R
| 2 => C3R

noncomputable
def exactVertex (idx : VertexIndex) :=
  (-1)^idx.ℓ.val • RzL (2 * π * (idx.k : ℝ) / 15) (Cpt idx.i)

lemma exactVertex_eq_vec (k : Fin 15) (ℓ : Fin 2) (i : Fin 3) :
    let θ := 2 * π * (k : ℝ) / 15
    exactVertex ⟨k, ℓ, i⟩ =
      (-1)^ℓ.val •
        !₂[cos θ * Cpt i 0 - sin θ * Cpt i 1,
           sin θ * Cpt i 0 + cos θ * Cpt i 1,
           Cpt i 2] := by
  simp only [exactVertex, Int.reduceNeg, RzL, Matrix.toEuclideanLin, Matrix.toLpLin, Rz_mat,
    LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', LinearEquiv.arrowCongr_apply,
    LinearEquiv.symm_symm, WithLp.linearEquiv_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, WithLp.addEquiv_apply, Matrix.toLin'_apply, Matrix.cons_mulVec,
    Matrix.cons_dotProduct, Matrix.vecHead, Fin.isValue, Matrix.vecTail, Nat.succ_eq_add_one,
    Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, neg_mul, Fin.succ_one_eq_two,
    zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, one_mul, zero_add, Matrix.empty_mulVec,
    WithLp.linearEquiv_symm_apply, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
    WithLp.addEquiv_symm_apply]
  ring_nf

noncomputable
def exactVerts : Finset ℝ³ := Finset.image exactVertex Finset.univ

lemma exactVerts_nonempty : exactVerts.Nonempty := by
  use exactVertex 0
  simp [exactVerts]

def exactVerts_nontriv : ∀ v ∈ exactVerts, 0 < ‖v‖ := by
  intro v hv
  simp only [exactVerts, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨j, hj⟩ := hv
  rw [← hj]
  simp only [exactVertex, Int.reduceNeg]
  rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Bounding.Rz_preserves_norm]
  generalize h : j.i = s
  fin_cases s
  · simp [Cpt, c1_norm_one]
  · simp only [Cpt]
    grind [c2_norm_bound]
  · simp only [Cpt]
    grind [c3_norm_bound]

def exactVertSet : Set ℝ³ := exactVerts

noncomputable
abbrev exactHull : Set ℝ³ := convexHull ℝ exactVerts

lemma exactVertex_norm_le_one (j : VertexIndex) : ‖exactVertex j‖ ≤ 1 := by
  simp only [exactVertex, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Bounding.Rz_preserves_norm]
  generalize h : j.i = s
  fin_cases s
  · simp [Cpt, c1_norm_one]
  · simp [Cpt, c2_norm_le_one]
  · simp [Cpt, c3_norm_le_one]

/--
The radius of the noperthedron is 1.
-/
theorem exactVertex_radius_one : Polyhedron.radius ⟨exactVertex⟩ = 1 := by
  rw [Polyhedron.radius_iff]
  constructor
  · use ⟨0, 0, 0⟩
    simp [exactVertex, exactVertex, Cpt, Bounding.Rz_preserves_norm, c1_norm_one]
  · intro j
    exact exactVertex_norm_le_one j

noncomputable
def exactPolyhedron : Polyhedron VertexIndex ℝ³ := {
  v := exactVertex
}

theorem exactPolyhedron_point_symmetric : PointSym exactPolyhedron.hull := by
  simp only [exactPolyhedron, Polyhedron.hull]
  simp only [exactVertex, Int.reduceNeg] at *
  refine hull_preserves_pointsym ?_
  rintro x ⟨j, hj⟩
  obtain ⟨k, ℓ, i⟩ := j
  exact ⟨⟨k, 1 - ℓ, i⟩, by rw [← hj]; fin_cases ℓ <;> simp [neg_smul]⟩

lemma exactPolyhedron_hull : exactPolyhedron.hull = exactHull := by
  simp only [Polyhedron.hull, exactPolyhedron, exactHull, exactVerts, Finset.coe_image,
    Finset.coe_univ, Set.image_univ]
  congr

noncomputable
def exactPoly : GoodPoly VertexIndex := {
  vertices := exactPolyhedron,
  nontriv := by
    rintro j
    refine exactVerts_nontriv _ ?_
    simp [exactVerts, exactPolyhedron]
  radius_eq_one := exactVertex_radius_one
}

theorem exactVerts_pointsym : PointSym exactVertSet := by
  intro x hx
  simp only [exactVertSet, exactVerts, Finset.coe_image, exactVertex, Int.reduceNeg,
    Finset.coe_univ, Set.image_univ, Set.mem_range] at *
  obtain ⟨y, hy⟩ := hx
  obtain ⟨k, ℓ, i⟩ := y
  exact ⟨⟨k, 1 - ℓ, i⟩, by rw [← hy]; fin_cases ℓ <;> simp [neg_smul]⟩

/--
The noperthedron is pointsymmetric.
-/
theorem exactPoly_point_symmetric : PointSym exactPoly.hull := by
  simp only [exactPoly, GoodPoly.hull, Polyhedron.hull]
  simp only [exactVertex, exactPolyhedron, Int.reduceNeg] at *
  refine hull_preserves_pointsym ?_
  rintro x ⟨j, hj⟩
  obtain ⟨k, ℓ, i⟩ := j
  exact ⟨⟨k, 1 - ℓ, i⟩, by rw [← hj]; fin_cases ℓ <;> simp [neg_smul]⟩
