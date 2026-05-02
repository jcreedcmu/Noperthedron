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

def linearIndVerts : Set (Fin 3 → ℚ) := {2 * C1, C1 + C2, C1 + C3}
def affineIndVerts : Set (Fin 3 → ℚ) := {-C1, C1, C2, C3}

def linearIndVertsNonzero : ∀ v ∈ linearIndVerts, v ≠ 0 := by
  intro v hv
  simp [linearIndVerts] at hv
  obtain rfl | rfl | rfl := hv
  · intro h; simp [C1] at h; apply_fun (· 0) at h; simp at h;
  · intro h; simp [C1, C2] at h; apply_fun (· 0) at h; simp at h; norm_num at h
  · intro h; simp [C1, C3] at h; apply_fun (· 0) at h; simp at h; norm_num at h

theorem linearInd_key :
    LinearIndependent ℚ (fun v => v : linearIndVerts → Fin 3 → ℚ) := by
  sorry

theorem affineInd_key :
    AffineIndependent ℚ (fun p => p : ({-C1} ∪ (fun v => v +ᵥ (-C1)) '' linearIndVerts : Set (Fin 3 → ℚ))
        → (Fin 3 → ℚ)) := by
   rw [← linearIndependent_set_iff_affineIndependent_vadd_union_singleton]
   · exact linearInd_key
   · exact linearIndVertsNonzero

lemma neg_c1_cup_eq_affineIndVerts :
    ({-C1} ∪ (fun v => v +ᵥ (-C1)) '' linearIndVerts) = affineIndVerts := by
  simp only [linearIndVerts, affineIndVerts, Set.image_insert_eq, Set.image_singleton,
             vadd_eq_add, Set.union_insert, Set.union_singleton]
  ring_nf
  ext
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem affineIndVertsAffine : AffineIndependent ℚ (fun p => p : affineIndVerts → (Fin 3 → ℚ)) := by
  rw [← neg_c1_cup_eq_affineIndVerts]
  exact affineInd_key

theorem interior_exactVerts_null_nonempty :
    (interior ((convexHull ℝ) (exactVerts : Set (Euc(3))))).Nonempty := by
  sorry
