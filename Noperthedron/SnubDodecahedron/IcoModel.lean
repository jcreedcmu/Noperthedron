module

public import Noperthedron.SnubDodecahedron.IcoGroup
public import Noperthedron.SnubDodecahedron.Vertices

@[expose] public section

/-!
# Icosahedral models

The vertex slots of the solid are I-orbits (generated tables, IcoGroupData.lean):
orbit `o` has a base point, and slot i is g_i · (the base point of its orbit
`vOrbit i`), with g_i = `vertexElementIndex[i]`. An orbit's base point may be
fixed by a subgroup of I (`orbitStabilizer`): a point on a 5-fold or 3-fold
axis. An `IModel` is any choice of base points, each fixed by its stabilizer,
whose orbit slots lie within `modelErrorQ` of the rational model. It is a
`C5Model` (slot S k + s is Rz(2π/5)^k · slot s, S the number of seeds), and
its hull is invariant under all 60 rotations, `IModel.icoMatrix_image_hull`.
The certificates cover every `IModel`; the true solid is one.
-/

namespace Noperthedron.SnubDodecahedron

open scoped Matrix

/-- The number of seeds (vertex slots per C5 orbit). -/
abbrev seedCount : Nat := Fintype.card SeedIndex

def vElem (i : Nat) : Nat := vertexElementIndex.getD i 0

def icoInv (g : Nat) : Nat := icoInverseIndex.getD g 0

/-- The I-orbit of slot `i`. -/
def vOrbitN (i : Nat) : Nat := vertexOrbitIndex.getD i 0

def vOrbit (i : Nat) : Fin orbitCount := ⟨vOrbitN i % orbitCount, Nat.mod_lt _ (by decide)⟩

/-- The stabilizer of orbit `o`'s base point. -/
def icoStab (o : Nat) : List Nat := orbitStabilizer.getD o []

def oSlot (o k : Nat) : Nat := (orbitSlot.getD o []).getD k 0

def oStab (o k : Nat) : Nat := (orbitStab.getD o []).getD k 0

/-! ### Decided facts -/

/-- Every slot has an element of I and an orbit, and the orbits are
rotation-major: g_{S(k+1)+s} = Rz · g_{Sk+s} in the same orbit. -/
def vElemCheck : Bool :=
  (List.range (Fintype.card VertexIndex)).all fun i =>
    decide (vElem i < 60) && decide (vOrbitN i < orbitCount)

def vElemRzCheck : Bool :=
  (List.range (Fintype.card VertexIndex - seedCount)).all fun i =>
    decide (M3.mul8 (icoEntry icoRzIndex) (icoEntry (vElem i)) =
      M3.scale 160 (icoEntry (vElem (i + seedCount)))) &&
    decide (vOrbitN (i + seedCount) = vOrbitN i)

/-- For each orbit `o` and element k: k = g_j · h with j = `oSlot o k` a slot
of orbit `o` and h = `oStab o k` in the stabilizer. -/
def orbitSlotCheck : Bool :=
  (List.range orbitCount).all fun o => (List.range 60).all fun k =>
    decide (oSlot o k < Fintype.card VertexIndex) && decide (vOrbitN (oSlot o k) = o) &&
      decide (oStab o k ∈ icoStab o) &&
      decide (M3.mul8 (icoEntry (vElem (oSlot o k))) (icoEntry (oStab o k)) =
        M3.scale 160 (icoEntry k))

/-- `icoInv g` is the transpose of `g`. -/
def icoInvCheck : Bool :=
  (List.range 60).all fun g =>
    decide (icoInv g < 60) && decide (icoEntry (icoInv g) = M3.transpose (icoEntry g))

theorem vElemCheck_eq : vElemCheck = true := by decide +kernel

theorem vElemRzCheck_eq : vElemRzCheck = true := by decide +kernel

theorem orbitSlotCheck_eq : orbitSlotCheck = true := by decide +kernel

theorem icoInvCheck_eq : icoInvCheck = true := by decide +kernel

theorem vElem_lt {i : Nat} (hi : i < Fintype.card VertexIndex) : vElem i < 60 := by
  have hc := vElemCheck_eq
  simp only [vElemCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  exact (hc i hi).1

theorem ico_rz_mul_vElem {i : Nat} (hi : i < Fintype.card VertexIndex - seedCount) :
    ico icoRzIndex * ico (vElem i) = ico (vElem (i + seedCount)) ∧
      vOrbit (i + seedCount) = vOrbit i := by
  have hc := vElemRzCheck_eq
  simp only [vElemRzCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨hm, ho⟩ := hc i hi
  exact ⟨ico_mul_of_mul8 hm, Fin.ext (by simp only [vOrbit]; rw [ho])⟩

theorem orbitSlot_spec {o k : Nat} (ho : o < orbitCount) (hk : k < 60) :
    oSlot o k < Fintype.card VertexIndex ∧ vOrbit (oSlot o k) = ⟨o, ho⟩ ∧
      oStab o k ∈ icoStab o ∧ ico (vElem (oSlot o k)) * ico (oStab o k) = ico k := by
  have hc := orbitSlotCheck_eq
  simp only [orbitSlotCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc o ho k hk
  exact ⟨h1, Fin.ext (by simp [vOrbit, h2, Nat.mod_eq_of_lt ho]), h3, ico_mul_of_mul8 h4⟩

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

/-- Base points for the I-orbits, each fixed by its stabilizer, whose orbit
slots are within `modelErrorQ` of the rational model. -/
structure IModel where
  v0 : Fin orbitCount → ℝ³
  fixed : ∀ o : Fin orbitCount, ∀ h ∈ icoStab o.val, (ico h).toEuclideanLin (v0 o) = v0 o
  close : ∀ i : VertexIndex,
    ‖(ico (vElem i.val)).toEuclideanLin (v0 (vOrbit i.val)) - toR3 (rationalVertex i)‖ ≤
      (modelErrorQ : ℝ)

namespace IModel

variable (P : IModel)

/-- Slot `n`: `ico (vElem n) · v0 (vOrbit n)`. -/
noncomputable def orbit (n : Nat) : ℝ³ := (ico (vElem n)).toEuclideanLin (P.v0 (vOrbit n))

theorem toEuclideanLin_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    (A * B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private theorem RzL_apply_add (α β : ℝ) (v : ℝ³) :
    RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

/-- Slot S k + s is Rz(2πk/5) · slot s. -/
theorem orbit_rotationMajor (k s : Nat) (hk : k < 5) (hs : s < seedCount) :
    P.orbit (seedCount * k + s) = RzL (2 * Real.pi * (k : ℝ) / 5) (P.orbit s) := by
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
      obtain ⟨hstep, horbit⟩ := ico_rz_mul_vElem (i := seedCount * k + s)
        (by simp only [Fintype.card_fin] at hs ⊢; omega)
      have hangle : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / 5 =
          2 * Real.pi / 5 + 2 * Real.pi * (k : ℝ) / 5 := by
        push_cast
        ring
      rw [hangle, RzL_apply_add, ← ih (by omega), orbit, orbit,
        show seedCount * (k + 1) + s = seedCount * k + s + seedCount by ring, ← hstep, horbit,
        toEuclideanLin_mul, ico_rz]
      rfl

theorem slot_eq (i : VertexIndex) :
    seedCount * (orbitIndex i).val + (seedIndex i).val = i.val := by
  simp only [orbitIndex, seedIndex, seedCount, Fintype.card_fin]
  omega

/-- The fivefold model with seeds `orbit s`. -/
noncomputable def toC5 : C5Model where
  seed s := P.orbit s.val
  close i := by
    have h := P.orbit_rotationMajor (orbitIndex i).val (seedIndex i).val
      (orbitIndex i).isLt (by simp [seedCount])
    rw [slot_eq] at h
    rw [← h]
    exact P.close i

theorem toC5_vertex (i : VertexIndex) : P.toC5.vertex i = P.orbit i.val := by
  have h := P.orbit_rotationMajor (orbitIndex i).val (seedIndex i).val
    (orbitIndex i).isLt (by simp [seedCount])
  rw [slot_eq] at h
  rw [h]
  rfl

/-- A rotation of I moves each vertex to a vertex. -/
theorem exists_ico_vertex {g : Nat} (hg : g < 60) (i : VertexIndex) :
    ∃ j : VertexIndex, (ico g).toEuclideanLin (P.toC5.vertex i) = P.toC5.vertex j := by
  obtain ⟨k, hk, hmul⟩ := exists_ico_mul g (vElem i.val) hg (vElem_lt i.isLt)
  set o := vOrbit i.val
  obtain ⟨hj, hjo, hh, hjh⟩ := orbitSlot_spec o.isLt hk
  refine ⟨⟨oSlot o k, hj⟩, ?_⟩
  rw [toC5_vertex, toC5_vertex, orbit, orbit, ← toEuclideanLin_mul, hmul, ← hjh,
    toEuclideanLin_mul, P.fixed o _ hh]
  simp only [hjo]

/-- Every rotation of I maps the vertex set onto itself. -/
theorem icoMatrix_image_verts (g : IcoIndex) :
    (icoMatrix g).toEuclideanLin '' (P.toC5.verts : Set ℝ³) = P.toC5.verts := by
  ext x
  simp only [C5Model.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := P.exists_ico_vertex g.isLt i
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    -- vertex j = g · (g⁻¹ · vertex j).
    obtain ⟨hinv, hone⟩ := ico_mul_icoInv g.isLt
    obtain ⟨i, hi⟩ := P.exists_ico_vertex hinv j
    refine ⟨P.toC5.vertex i, ⟨i, rfl⟩, ?_⟩
    rw [← hi, icoMatrix, ← toEuclideanLin_mul, hone]
    simp

theorem icoMatrix_image_hull (g : IcoIndex) :
    (icoMatrix g).toEuclideanLin '' P.toC5.polyhedron.hull = P.toC5.polyhedron.hull := by
  rw [P.toC5.polyhedron_hull, LinearMap.image_convexHull, P.icoMatrix_image_verts g]

end IModel

end Noperthedron.SnubDodecahedron
