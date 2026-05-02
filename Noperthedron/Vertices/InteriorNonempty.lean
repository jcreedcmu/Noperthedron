import Noperthedron.Basic
import Noperthedron.Bounding
import Noperthedron.PointSym
import Noperthedron.Vertices.Index
import Noperthedron.Vertices.Exact

/-!
This file proves the interior of the Noperthedron is nonempty.
-/

open scoped Matrix

namespace Noperthedron

open Real

def n1a : ℤ := 152024884
def n1b : ℤ := 210152163
def d1  : ℤ := 259375205

def n2a : ℤ := 6632738028
def n2b : ℤ := 6106948881
def n2c : ℤ := 3980949609
def d2  : ℤ := 10^10

def n3a : ℤ := 8193990033
def n3b : ℤ := 5298215096
def n3c : ℤ := 1230614493
-- we don't define d3, it's the same as d2

def M_int : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2 * d2 * n1a,  d1 * n2a + d2 * n1a,  d1 * n3a + d2 * n1a;
     0,             d1 * n2b,             d1 * n3b;
     2 * d2 * n1b,  d1 * n2c + d2 * n1b,  d1 * n3c + d2 * n1b]

def M_rat : Matrix (Fin 3) (Fin 3) ℚ :=
  !![2 * n1a / d1,  n2a / d2 + n1a / d1,  n3a / d2 + n1a / d1;
     0,             n2b / d2,             n3b / d2;
     2 * n1b / d1,  n2c / d2 + n1b / d1,  n3c / d2 + n1b / d1]

theorem M_int_det_ne_zero : M_int.det ≠ 0 := by decide

theorem M_int_cast_eq :
    M_int.map (Int.cast : ℤ → ℚ) = (↑d1 * ↑d2) • M_rat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [M_int, M_rat, d1, d2, n1a, n1b, n2a, n2b, n2c, n3a, n3b, n3c] <;> ring

theorem M_rat_det_ne_zero : M_rat.det ≠ 0 := by
  intro h
  refine M_int_det_ne_zero ?_
  have h2 : (M_int.det : ℚ) = (d1 * d2) ^ Fintype.card (Fin 3) • M_rat.det := by
    rw [Int.cast_det, M_int_cast_eq, Matrix.det_smul_of_tower]
  simp [h] at h2
  exact_mod_cast h2

theorem M_real_det_ne_zero : (M_rat.map (Rat.cast : ℚ → ℝ)).det ≠ 0 := by
  rw [← Rat.cast_det]; exact_mod_cast M_rat_det_ne_zero

noncomputable def C1ℝ : Fin 3 → ℝ := fun i => (C1 i : ℝ)
noncomputable def C2ℝ : Fin 3 → ℝ := fun i => (C2 i : ℝ)
noncomputable def C3ℝ : Fin 3 → ℝ := fun i => (C3 i : ℝ)

def linearIndVerts : Set (Fin 3 → ℝ) := {2 * C1ℝ, C1ℝ + C2ℝ, C1ℝ + C3ℝ}

def linearIndVertsNonzero : ∀ v ∈ linearIndVerts, v ≠ 0 := by
  intro v hv
  simp [linearIndVerts] at hv
  obtain rfl | rfl | rfl := hv
  · intro h; apply_fun (· 0) at h; simp [C1ℝ, C1] at h
  · intro h; apply_fun (· 0) at h; simp [C1ℝ, C2ℝ, C1, C2] at h; norm_num at h
  · intro h; apply_fun (· 0) at h; simp [C1ℝ, C3ℝ, C1, C3] at h; norm_num at h

theorem M_real_cols_eq :
    (M_rat.map (Rat.cast : ℚ → ℝ)).col = ![2 * C1ℝ, C1ℝ + C2ℝ, C1ℝ + C3ℝ] := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [Matrix.col, M_rat, C1ℝ, C2ℝ, C3ℝ, C1, C2, C3,
          d1, d2, n1a, n1b, n2a, n2b, n2c, n3a, n3b, n3c]
  all_goals ring_nf

theorem linearIndVerts_hrange :
    Set.range ![2 * C1ℝ, C1ℝ + C2ℝ, C1ℝ + C3ℝ] = linearIndVerts := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.union_singleton, Set.union_insert, linearIndVerts]
  ext
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem linearInd_key :
    LinearIndependent ℝ (fun v => v : linearIndVerts → Fin 3 → ℝ) := by
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero M_real_det_ne_zero
  rw [M_real_cols_eq] at hli
  rw [linearIndependent_subtype_iff, ← linearIndVerts_hrange]
  exact (linearIndepOn_range_iff hli.injective id).mpr hli

theorem affineInd_key :
    AffineIndependent ℝ (fun p => p :
      ({-C1ℝ} ∪ (fun v => v +ᵥ (-C1ℝ)) '' linearIndVerts : Set (Fin 3 → ℝ)) → (Fin 3 → ℝ)) := by
  rw [← linearIndependent_set_iff_affineIndependent_vadd_union_singleton]
  · exact linearInd_key
  · exact linearIndVertsNonzero

def affineIndVertsR : Set (Fin 3 → ℝ) := {-C1ℝ, C1ℝ, C2ℝ, C3ℝ}

lemma neg_c1_cup_eq_affineIndVerts :
    ({-C1ℝ} ∪ (fun v => v +ᵥ (-C1ℝ)) '' linearIndVerts) = affineIndVertsR := by
  simp only [linearIndVerts, affineIndVertsR, Set.image_insert_eq, Set.image_singleton,
             vadd_eq_add, Set.union_insert, Set.union_singleton]
  ring_nf
  ext
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem affineIndVertsAffine :
    AffineIndependent ℝ (fun p => p : affineIndVertsR → (Fin 3 → ℝ)) := by
  rw [← neg_c1_cup_eq_affineIndVerts]
  exact affineInd_key

theorem interior_exactVerts_hull_nonempty :
    (interior ((convexHull ℝ) (exactVerts : Set (Euc(3))))).Nonempty := by
  sorry
