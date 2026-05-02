import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
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

def linearIndVerts : Fin 3 → (Fin 3 → ℚ) := ![2 * C1, C1 + C2, C1 + C3]
def affineIndVerts : Fin 4 → (Fin 3 → ℚ) := ![C1, C2, C3, -C1]
noncomputable
def affineIndVertsR : Fin 4 → Euc(3) := ![C1R, C2R, C3R, -C1R]

theorem M_rat_cols_eq : M_rat.col = ![2 * C1, C1 + C2, C1 + C3] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [M_rat, C1, C2, C3, Matrix.col, d1, d2, n1a, n1b, n2a, n2b, n2c, n3a, n3b, n3c] <;> ring

theorem linearIndVerts_eq_M_rat_transpose (i j : Fin 3) : linearIndVerts i j = M_rat j i := by
  simp only [linearIndVerts, M_rat, C1, C2, C3, d1, d2, n1a, n1b, n2a, n2b, n2c, n3a, n3b, n3c]
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf

theorem linearIndR_key :
    LinearIndependent ℝ (fun i : Fin 3 => WithLp.toLp 2 (fun j => (linearIndVerts i j : ℝ))) := by
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero M_real_det_ne_zero
  have heq : (fun i => WithLp.toLp 2 fun j => (linearIndVerts i j : ℝ)) =
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm ∘ (M_rat.map Rat.cast).col   := by
     ext i j;
     push_cast;
     simp [linearIndVerts_eq_M_rat_transpose];
  rw [heq]
  exact hli.map' _ (LinearEquiv.ker _)

theorem affineIndVertsRAffine : AffineIndependent ℝ affineIndVertsR := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ affineIndVertsR 3]
  rw [← linearIndependent_equiv (finSuccAboveEquiv 3)]
  convert linearIndR_key using 1
  ext1 i; fin_cases i
    <;> simp [affineIndVertsR, linearIndVerts, finSuccAboveEquiv, Fin.succAbove]
    <;> ring_nf
  · rw [C1R]; ext; simp; ring_nf
  · rw [C1R, C2R]; ext; simp; ring_nf
  · rw [C1R, C3R]; ext; simp; ring_nf

theorem affineIndVertsR_span_eq_top :
    affineSpan ℝ (Set.range affineIndVertsR) = ⊤ := by
  rw [affineIndVertsRAffine.affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp [Fintype.card_fin]

/-- RzL at angle 0 is the identity. -/
lemma RzL_zero_eq_one : RzL (0 : ℝ) = 1 :=
  AddChar.map_zero_eq_one RzC

/--
All of the vertices we are showing to be affine independent actually
occur in the Noperthedron.
-/
theorem affineIndVertsR_subset_exactVerts :
    Set.range affineIndVertsR ⊆ (exactVerts : Set Euc(3)) := by
  rintro x ⟨i, rfl⟩
  fin_cases i <;>
    simp only [affineIndVertsR, exactVerts, Finset.coe_image] <;>
    [use ⟨0, 0, 0⟩; use ⟨0, 0, 1⟩; use ⟨0, 0, 2⟩; use ⟨0, 1, 0⟩] <;>
    simp [RzL_zero_eq_one, exactVertex, Cpt]

theorem exactVerts_affineSpan_eq_top :
    affineSpan ℝ (exactVerts : Set Euc(3)) = ⊤ := by
  rw [eq_top_iff, ← affineIndVertsR_span_eq_top]
  exact affineSpan_mono ℝ affineIndVertsR_subset_exactVerts

theorem interior_exactVerts_hull_nonempty :
    (interior ((convexHull ℝ) (exactVerts : Set (Euc(3))))).Nonempty :=
by
  exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    exactVerts_affineSpan_eq_top
