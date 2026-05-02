import Noperthedron.Basic
import Noperthedron.Bounding
import Noperthedron.PointSym
import Noperthedron.Vertices.Index
import Noperthedron.Vertices.Exact
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

set_option doc.verso true
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
noncomputable
def affineIndVertsR : Fin 4 → Euc(3) := ![-C1R, C1R, C2R, C3R]

def linearIndVertsNonzero : ∀ v ∈ linearIndVerts, v ≠ 0 := by
  intro v hv
  simp [linearIndVerts] at hv
  obtain rfl | rfl | rfl := hv
  · intro h; simp [C1] at h; apply_fun (· 0) at h; simp at h;
  · intro h; simp [C1, C2] at h; apply_fun (· 0) at h; simp at h; norm_num at h
  · intro h; simp [C1, C3] at h; apply_fun (· 0) at h; simp at h; norm_num at h

theorem M_rat_cols_eq : M_rat.col = ![2 * C1, C1 + C2, C1 + C3] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [M_rat, C1, C2, C3, Matrix.col, d1, d2, n1a, n1b, n2a, n2b, n2c, n3a, n3b, n3c] <;> ring

theorem linearIndVerts_hrange : Set.range ![2 * C1, C1 + C2, C1 + C3] = linearIndVerts := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.union_singleton, Set.union_insert, linearIndVerts]
  ext
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff];
  tauto

theorem linearInd_key :
      LinearIndependent ℚ (fun v => v : linearIndVerts → Fin 3 → ℚ) := by
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero M_rat_det_ne_zero
  rw [M_rat_cols_eq] at hli
  rw [linearIndependent_subtype_iff, ← linearIndVerts_hrange]
  exact (linearIndepOn_range_iff hli.injective id).mpr hli

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

/--
This is an impedance matching gap that should be filled by appealing to {name}`affineIndVertsAffine`
-/
theorem affineIndVertsRAffine : AffineIndependent ℝ affineIndVertsR := by
  sorry

theorem affineIndVertsR_span_eq_top :
    affineSpan ℝ (Set.range affineIndVertsR) = ⊤ := by
  rw [affineIndVertsRAffine.affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp [Fintype.card_fin]

theorem affineIndVertsR_subset_exactVerts :
    Set.range affineIndVertsR ⊆ (exactVerts : Set Euc(3)) := by
  rintro x ⟨i, rfl⟩
  fin_cases i
  all_goals simp [exactVerts]
  · sorry
  · sorry
  · sorry
  · sorry

theorem exactVerts_affineSpan_eq_top :
    affineSpan ℝ (exactVerts : Set Euc(3)) = ⊤ := by
  rw [eq_top_iff, ← affineIndVertsR_span_eq_top]
  exact affineSpan_mono ℝ affineIndVertsR_subset_exactVerts

-- Step 4: interior nonempty
theorem interior_exactVerts_null_nonempty :
    (interior ((convexHull ℝ) (exactVerts : Set (Euc(3))))).Nonempty :=
by
  exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    exactVerts_affineSpan_eq_top
