module

public import Noperthedron.Nopert231.IcoGroup
public import Noperthedron.Nopert231.Vertices

@[expose] public section

/-!
# Icosahedral models

The snub dodecahedron's 60 vertices are a free orbit of the icosahedral
rotation group I: vertex i = g_i · vertex 0, with g_i = `vertexElement i`
(generated, IcoGroupData.lean). An `IModel` is any point `v0` whose I-orbit,
in that order, lies within `modelErrorQ` of the rational model. It is a
`C5Model` (vertex 12k + s is Rz(2π/5)^k · vertex s), and its hull is
invariant under all 60 rotations, `IModel.icoMatrix_image_hull`. The
certificates cover every `IModel`; the true snub dodecahedron is one.
-/

namespace Noperthedron.Nopert231

open scoped Matrix

def vElem (i : Nat) : Nat := vertexElementIndex.getD i 0

def elemV (k : Nat) : Nat := elementVertexIndex.getD k 0

def icoInv (g : Nat) : Nat := icoInverseIndex.getD g 0

/-! ### Decided facts -/

/-- `vElem` is a bijection of `range 60`, with inverse `elemV`. -/
def vElemCheck : Bool :=
  (List.range 60).all fun i =>
    decide (vElem i < 60) && decide (elemV (vElem i) = i) && decide (elemV i < 60) &&
      decide (vElem (elemV i) = i)

/-- Rotation-major order: g_{12(k+1)+s} = Rz · g_{12k+s}. -/
def vElemRzCheck : Bool :=
  (List.range 48).all fun i =>
    decide (M3.mul8 (icoEntry icoRzIndex) (icoEntry (vElem i)) =
      M3.scale 160 (icoEntry (vElem (i + 12))))

/-- `icoInv g` is the transpose of `g`. -/
def icoInvCheck : Bool :=
  (List.range 60).all fun g =>
    decide (icoInv g < 60) && decide (icoEntry (icoInv g) = M3.transpose (icoEntry g))

theorem vElemCheck_eq : vElemCheck = true := by decide +kernel

theorem vElemRzCheck_eq : vElemRzCheck = true := by decide +kernel

theorem icoInvCheck_eq : icoInvCheck = true := by decide +kernel

theorem vElem_lt {i : Nat} (hi : i < 60) : vElem i < 60 := by
  have hc := vElemCheck_eq
  simp only [vElemCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  exact (hc i hi).1.1.1

theorem vElem_elemV {k : Nat} (hk : k < 60) : elemV k < 60 ∧ vElem (elemV k) = k := by
  have hc := vElemCheck_eq
  simp only [vElemCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  exact ⟨(hc k hk).1.2, (hc k hk).2⟩

theorem ico_rz_mul_vElem {i : Nat} (hi : i < 48) :
    ico icoRzIndex * ico (vElem i) = ico (vElem (i + 12)) := by
  have hc := vElemRzCheck_eq
  simp only [vElemRzCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  exact ico_mul_of_mul8 (hc i hi)

theorem ico_mul_icoInv {g : Nat} (hg : g < 60) : icoInv g < 60 ∧ ico g * ico (icoInv g) = 1 := by
  have hc := icoInvCheck_eq
  simp only [icoInvCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨hlt, heq⟩ := hc g hg
  refine ⟨hlt, ?_⟩
  have htr : ico (icoInv g) = (ico g)ᵀ := by
    rw [ico, ico, heq, M3.toMatrix_transpose, Matrix.transpose_smul]
  rw [htr]
  exact Matrix.mul_eq_one_comm.mp (icoMatrix_transpose_mul ⟨g, hg⟩)

/-! ### Models -/

/-- A point whose I-orbit is within `modelErrorQ` of the rational model. -/
structure IModel where
  v0 : ℝ³
  close : ∀ i : VertexIndex,
    ‖(ico (vElem i.val)).toEuclideanLin v0 - toR3 (rationalVertex i)‖ ≤ (modelErrorQ : ℝ)

namespace IModel

variable (P : IModel)

/-- Orbit point `n`: `ico (vElem n) · v0`. -/
noncomputable def orbit (n : Nat) : ℝ³ := (ico (vElem n)).toEuclideanLin P.v0

theorem toEuclideanLin_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    (A * B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private theorem RzL_apply_add (α β : ℝ) (v : ℝ³) :
    RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

/-- Orbit point 12k + s is Rz(2πk/5) · orbit point s. -/
theorem orbit_rotationMajor (k s : Nat) (hk : k < 5) (hs : s < 12) :
    P.orbit (12 * k + s) = RzL (2 * Real.pi * (k : ℝ) / 5) (P.orbit s) := by
  induction k with
  | zero =>
      have hzero : RzL 0 = ContinuousLinearMap.id ℝ ℝ³ := by
        apply ContinuousLinearMap.ext
        intro v
        ext i
        fin_cases i <;>
          simp [RzL, Rz_mat, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]
      simp [hzero]
  | succ k ih =>
      have hstep := ico_rz_mul_vElem (i := 12 * k + s) (by omega)
      have hangle : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / 5 =
          2 * Real.pi / 5 + 2 * Real.pi * (k : ℝ) / 5 := by
        push_cast
        ring
      rw [hangle, RzL_apply_add, ← ih (by omega), orbit, orbit,
        show 12 * (k + 1) + s = 12 * k + s + 12 by ring, ← hstep, toEuclideanLin_mul, ico_rz]
      rfl

/-- The fivefold model with seeds `orbit s`. -/
noncomputable def toC5 : C5Model where
  seed s := P.orbit s.val
  close i := by
    have h := P.orbit_rotationMajor (orbitIndex i).val (seedIndex i).val
      (orbitIndex i).isLt (seedIndex i).isLt
    have hi : 12 * (orbitIndex i).val + (seedIndex i).val = i.val := by
      simp only [orbitIndex, seedIndex]
      omega
    rw [hi] at h
    rw [← h]
    exact P.close i

theorem toC5_vertex (i : VertexIndex) : P.toC5.vertex i = P.orbit i.val := by
  have h := P.orbit_rotationMajor (orbitIndex i).val (seedIndex i).val
    (orbitIndex i).isLt (seedIndex i).isLt
  have hi : 12 * (orbitIndex i).val + (seedIndex i).val = i.val := by
    simp only [orbitIndex, seedIndex]
    omega
  rw [hi] at h
  rw [h]
  rfl

/-- Every rotation of I maps the vertex set onto itself. -/
theorem icoMatrix_image_verts (g : IcoIndex) :
    (icoMatrix g).toEuclideanLin '' (P.toC5.verts : Set ℝ³) = P.toC5.verts := by
  -- g · orbit i = orbit (elemV k), where ico g * ico (vElem i) = ico k.
  have hmove : ∀ i : VertexIndex, ∃ j : VertexIndex,
      (icoMatrix g).toEuclideanLin (P.toC5.vertex i) = P.toC5.vertex j := by
    intro i
    obtain ⟨k, hk, hmul⟩ := exists_ico_mul g.val (vElem i.val) g.isLt (vElem_lt i.isLt)
    obtain ⟨hj, hvj⟩ := vElem_elemV hk
    refine ⟨⟨elemV k, hj⟩, ?_⟩
    rw [toC5_vertex, toC5_vertex, orbit, orbit, icoMatrix, ← toEuclideanLin_mul, hmul]
    simp only [hvj]
  ext x
  simp only [C5Model.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := hmove i
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    -- vertex j = g · (g⁻¹ · vertex j).
    obtain ⟨hinv, hone⟩ := ico_mul_icoInv g.isLt
    obtain ⟨k, hk, hmul⟩ := exists_ico_mul (icoInv g.val) (vElem j.val) hinv (vElem_lt j.isLt)
    obtain ⟨hi, hvi⟩ := vElem_elemV hk
    refine ⟨P.toC5.vertex ⟨elemV k, hi⟩, ⟨⟨elemV k, hi⟩, rfl⟩, ?_⟩
    rw [toC5_vertex, toC5_vertex, orbit, orbit, hvi, ← hmul, ← toEuclideanLin_mul,
      ← Matrix.mul_assoc, icoMatrix, hone, Matrix.one_mul]

theorem icoMatrix_image_hull (g : IcoIndex) :
    (icoMatrix g).toEuclideanLin '' P.toC5.polyhedron.hull = P.toC5.polyhedron.hull := by
  rw [P.toC5.polyhedron_hull, LinearMap.image_convexHull, P.icoMatrix_image_verts g]

end IModel

end Noperthedron.Nopert231
