import Noperthedron.Basic
import Noperthedron.Bounding
import Noperthedron.PointSym

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

end Nopert

namespace Noperthedron
open Real

noncomputable
def Cpt : Fin 3 → ℝ³
| 0 => Nopert.C1R
| 1 => Nopert.C2R
| 2 => Nopert.C3R

noncomputable
def exactPt (k ℓ : ℕ) (i : Fin 3) :=
  (-1)^ℓ • RzL (2 * π * (k : ℝ) / 15) (Cpt i)

noncomputable
def exactVertex (j : Fin 90) : ℝ³ :=
  exactPt (j.val % 15) (j.val / 45) ⟨(j.val % 45) / 15, by omega⟩

noncomputable
def exactVerts : Finset ℝ³ := Finset.image exactVertex Finset.univ

lemma exactVerts_nonempty : exactVerts.Nonempty := by simp [exactVerts]

def exactVerts_nontriv : ∀ v ∈ exactVerts, 0 < ‖v‖ := by
  intro v hv
  simp only [exactVerts, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨j, hj⟩ := hv
  rw [← hj]
  simp only [exactVertex, exactPt, Int.reduceNeg]
  rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Bounding.Rz_preserves_norm]
  generalize h : (⟨(j.val % 45) / 15, by omega⟩ : Fin 3) = s
  fin_cases s
  · simp [Cpt, Nopert.c1_norm_one]
  · simp only [Cpt]
    grind [Nopert.c2_norm_bound]
  · simp only [Cpt]
    grind [Nopert.c3_norm_bound]

def exactVertSet : Set ℝ³ := exactVerts

noncomputable
def exactShape : Shape where
  vertices := exactVerts

lemma exactPt_norm_le_one (k ℓ : ℕ) (i : Fin 3) : ‖exactPt k ℓ i‖ ≤ 1 := by
  simp only [exactPt, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Bounding.Rz_preserves_norm]
  fin_cases i
  · simp [Cpt, Nopert.c1_norm_one]
  · simp [Cpt, Nopert.c2_norm_le_one]
  · simp [Cpt, Nopert.c3_norm_le_one]

/--
The radius of the noperthedron is 1.
-/
theorem exactVerts_radius_one : polyhedronRadius exactVerts exactVerts_nonempty = 1 := by
  simp only [exactVerts]
  rw [polyhedron_radius_iff]
  constructor
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and]
    use 0
    simp [exactVertex, exactPt, Cpt, Bounding.Rz_preserves_norm, Nopert.c1_norm_one]
  · intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, exactVertex, true_and] at hv
    obtain ⟨x, hx⟩ := hv
    rw [←hx]
    exact exactPt_norm_le_one _ _ _

noncomputable
def exactPoly : GoodPoly := {
  vertices := exactVerts,
  nonempty := exactVerts_nonempty,
  nontriv := exactVerts_nontriv,
  radius_eq_one := exactVerts_radius_one
}

theorem exactVerts_pointsym : PointSym exactVertSet := by
  intro x hx
  simp only [exactVertSet, exactVerts, Finset.coe_image, exactVertex, exactPt, Int.reduceNeg,
    Finset.coe_univ, Set.image_univ, Set.mem_range] at *
  obtain ⟨y, hy⟩ := hx
  by_cases h : y.val < 45
  · refine ⟨⟨y.val + 45, by omega⟩, ?_⟩
    rw [← hy]
    have h1 : (y.val + 45) / 45 = 1 := by omega
    have h2 : y.val / 45 = 0 := by omega
    have h3 : (y.val + 45) % 15 = y.val % 15 := by omega
    have h4 : (y.val + 45) % 45 / 15 = y.val % 45 / 15 := by omega
    simp only [h1, h2, h3, h4]
    simp [pow_one, pow_zero, one_smul]
  · push Not at h
    refine ⟨⟨y.val - 45, by omega⟩, ?_⟩
    rw [← hy]
    have h1 : (y.val - 45) / 45 = 0 := by omega
    have h2 : y.val / 45 = 1 := by omega
    have h3 : (y.val - 45) % 15 = y.val % 15 := by omega
    have h4 : (y.val - 45) % 45 / 15 = y.val % 45 / 15 := by omega
    simp only [h1, h2, h3, h4]
    simp [pow_one, pow_zero, one_smul]

/--
The noperthedron is pointsymmetric.
-/
theorem exactShape_point_symmetric : PointSym exactShape.hull := by
  exact hull_preserves_pointsym exactVerts_pointsym
