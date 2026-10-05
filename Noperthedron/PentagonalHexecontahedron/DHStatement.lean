module

public import Noperthedron.PentagonalHexecontahedron.DHStatementData
public import Noperthedron.PentagonalHexecontahedron.CapRow
public import Noperthedron.PentagonalHexecontahedron.IcoInstance
public import Noperthedron.PentagonalHexecontahedron.HalfTurnPose

@[expose] public section

/-!
# The deltoidal hexecontahedron

`deltoidalHexecontahedron` is David McCooey's vertex set: the cyclic
permutations, with all sign changes, of five generating points with
coordinates in ℚ(√5) (62 points). A polyhedron is *a* deltoidal
hexecontahedron (`IsDeltoidalHexecontahedron`) when its vertices are the image
of that set under a similarity (an orthogonal map, possibly a reflection, a
positive scaling and a translation).

The exact solid in the model frame (`dhIModel`): the 70 vertex slots over
K = ℚ(√5, sin 72°) (`dhSlotK`, McCooey's scale), times the rational scale
`dhScale`. Decided over K:
- the frame rows `dhFrameK` are orthonormal (`frameCheck`), and the frame maps
  McCooey's points onto the slots and back (`mcCheck`, `slotMcCheck`);
- each slot i is `ico (vElem i)` applied to its orbit's base slot, and the
  base slots are fixed by their stabilizers (`orbitCheck`, `stabCheck`);
- the slots are closed under negation (`symCheck`): the solid is centrally
  symmetric;
and by interval arithmetic (`IModel.ofBoxes`), `dhScale` times each slot is
within `modelErrorQ` of `rationalVertex`. So `dhIModel` is an `IModel`, and
its vertex set is `dhScale · T(deltoidalHexecontahedron)`.

`dhHull_eq`: for any list of K-vectors with the same set as the slots (as a
cap certificate's vertex list, checked by `sameSlots`), the hull is
`dhScale · convexHull`, the form the cap theorem (`CapCert.claim`) uses.
-/

namespace Noperthedron.PentagonalHexecontahedron.DH

open NPoly PVec Cap
open scoped Matrix RealInnerProductSpace

/-! ### McCooey's coordinates -/

noncomputable def C0 : ℝ := (5 - √5) / 4
noncomputable def C1 : ℝ := (15 + √5) / 22
noncomputable def C2 : ℝ := √5 / 2
noncomputable def C3 : ℝ := (5 + √5) / 6
noncomputable def C4 : ℝ := (5 + 4 * √5) / 11
noncomputable def C5 : ℝ := (5 + √5) / 4
noncomputable def C6 : ℝ := (5 + 3 * √5) / 6
noncomputable def C7 : ℝ := (25 + 9 * √5) / 22
noncomputable def C8 : ℝ := √5

/-- McCooey's five generating points. -/
noncomputable def mcGen : Fin 5 → Fin 3 → ℝ :=
  ![![0, 0, C8], ![0, C1, C7], ![C3, 0, C6], ![C0, C2, C5], ![C4, C4, C4]]

/-- Sign pattern `s`: bit `i` set means coordinate `i` is negated. -/
def signOf (s : Fin 8) (i : Fin 3) : Bool := s.val.testBit i.val

/-- A McCooey vertex: generator `g` with signs `s`, cyclically shifted by `k`. -/
noncomputable def mcPoint (g : Fin 5) (s : Fin 8) (k : Fin 3) : ℝ³ :=
  WithLp.toLp 2 fun i => (if signOf s (i + k) then -1 else 1) * mcGen g (i + k)

/-- The deltoidal hexecontahedron (McCooey's coordinates): the cyclic
permutations of the five generators with all sign changes. -/
def deltoidalHexecontahedron : Set ℝ³ := {v | ∃ g s k, v = mcPoint g s k}

/-- A deltoidal hexecontahedron: the image of `deltoidalHexecontahedron` under a
similarity (an orthogonal map, possibly a reflection, a positive scaling and a
translation). -/
def IsDeltoidalHexecontahedron (V : Finset ℝ³) : Prop :=
  ∃ (c : ℝ³) (s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ), 0 < s ∧
    M ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧
    (V : Set ℝ³) = (fun x => c + s • M.toEuclideanLin x) '' deltoidalHexecontahedron

/-! ### The same over K -/

def mcGenK : Fin 5 → KVec :=
  ![![0, 0, ⟨0, 1, 0, 0⟩],
    ![0, ⟨15 / 22, 1 / 22, 0, 0⟩, ⟨25 / 22, 9 / 22, 0, 0⟩],
    ![⟨5 / 6, 1 / 6, 0, 0⟩, 0, ⟨5 / 6, 1 / 2, 0, 0⟩],
    ![⟨5 / 4, -1 / 4, 0, 0⟩, ⟨0, 1 / 2, 0, 0⟩, ⟨5 / 4, 1 / 4, 0, 0⟩],
    ![⟨5 / 11, 4 / 11, 0, 0⟩, ⟨5 / 11, 4 / 11, 0, 0⟩, ⟨5 / 11, 4 / 11, 0, 0⟩]]

def mcK (g : Fin 5) (s : Fin 8) (k : Fin 3) : KVec := fun i =>
  if signOf s (i + k) then -(mcGenK g (i + k)) else mcGenK g (i + k)

theorem kv_mcGenK (g : Fin 5) : kv (mcGenK g) = mcGen g := by
  have h5 : IcoZ.sqrt5 = √5 := rfl
  funext i
  fin_cases g <;> fin_cases i <;>
    simp [kv, PVec.kval, mcGenK, mcGen, IcoQ.val, h5, C0, C1, C2, C3, C4, C5, C6, C7, C8,
      show (0 : IcoQ) = ⟨0, 0, 0, 0⟩ from rfl] <;> ring

theorem kv_mcK (g : Fin 5) (s : Fin 8) (k : Fin 3) : kv (mcK g s k) = (mcPoint g s k).ofLp := by
  funext i
  have hg := congrFun (kv_mcGenK g) (i + k)
  simp only [kv, PVec.kval, mcK, mcPoint] at hg ⊢
  split_ifs <;> simp [hg]

/-! ### Exact checks over K -/

/-- Equality of K-vectors, coordinatewise (kernel-friendly). -/
def keq (a b : KVec) : Bool := decide (a 0 = b 0) && decide (a 1 = b 1) && decide (a 2 = b 2)

theorem eq_of_keq {a b : KVec} (h : keq a b = true) : a = b := by
  simp only [keq, Bool.and_eq_true, decide_eq_true_eq] at h
  funext i
  fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

def dotK (a b : KVec) : IcoQ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

theorem val_dotK (a b : KVec) : (dotK a b).val = rdot (kv a) (kv b) := by
  simp [dotK, rdot, kv, PVec.kval]

def slotK (j : Nat) : KVec := dhSlotK.getD j 0
def frameRow (i : Fin 3) : KVec := dhFrameK.getD i.val 0

/-- T v over K (rows `frameRow`). -/
def frameApplyK (v : KVec) : KVec := fun i => dotK (frameRow i) v

/-- T as a real matrix. -/
noncomputable def frameMat : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (frameRow i j).val

theorem kv_frameApplyK (v : KVec) : kv (frameApplyK v) = frameMat *ᵥ kv v := by
  funext i
  simp only [kv, PVec.kval, frameApplyK, val_dotK, rdot, frameMat, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.of_apply]

/-- The frame rows are orthonormal. -/
def frameCheck : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    decide (dotK (frameRow i) (frameRow j) = if i = j then 1 else 0)

theorem frameCheck_eq : frameCheck = true := by decide +kernel

theorem frameMat_orthogonal : frameMat ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have hc := frameCheck_eq
  simp only [frameCheck, List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] at hc
  ext i j
  have h := congrArg IcoQ.val (hc i j)
  rw [val_dotK] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.transpose_apply, Fin.sum_univ_three,
    Matrix.one_apply, frameMat, Matrix.of_apply]
  simp only [rdot, kv, PVec.kval] at h
  rw [h]
  split_ifs <;> simp

/-- All (generator, signs, shift) triples. -/
def mcIndices : List (Fin 5 × Fin 8 × Fin 3) :=
  (List.finRange 5).flatMap fun g => (List.finRange 8).flatMap fun s => (List.finRange 3).map fun k => (g, s, k)

theorem mem_mcIndices (g : Fin 5) (s : Fin 8) (k : Fin 3) : (g, s, k) ∈ mcIndices := by
  simp [mcIndices]

/-- T maps every McCooey point to a slot. -/
def mcCheck : Bool :=
  mcIndices.all fun ⟨g, s, k⟩ => (List.range 70).any fun j => keq (frameApplyK (mcK g s k)) (slotK j)

/-- Every slot is T of a McCooey point. -/
def slotMcCheck : Bool :=
  (List.range 70).all fun j => mcIndices.any fun ⟨g, s, k⟩ => keq (frameApplyK (mcK g s k)) (slotK j)

theorem mcCheck_eq : mcCheck = true := by decide +kernel
theorem slotMcCheck_eq : slotMcCheck = true := by decide +kernel

/-- `ico n` over K. -/
def icoKN (n : Nat) (i j : Fin 3) : IcoQ :=
  let z := (icoEntry n).entry i j
  ⟨(z.a : ℚ) / 20, (z.b : ℚ) / 20, (z.c : ℚ) / 20, (z.d : ℚ) / 20⟩

def icoApplyK (n : Nat) (v : KVec) : KVec := fun i => dotK (icoKN n i) v

theorem kv_icoApplyK (n : Nat) (v : KVec) : kv (icoApplyK n v) = ico n *ᵥ kv v := by
  funext i
  simp only [kv, PVec.kval, icoApplyK, val_dotK, rdot, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have he : ∀ j, (icoKN n i j).val = ico n i j := by
    intro j
    simp only [icoKN, IcoQ.val, ico, M3.toMatrix, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, IcoZ.val]
    push_cast
    ring
  rw [he, he, he]

/-- Slot i is `ico (vElem i)` times its orbit's base slot. -/
def orbitCheck : Bool :=
  (List.range 70).all fun i => keq (icoApplyK (vElem i) (slotK (vOrbit i).val)) (slotK i)

/-- The base slots are fixed by their stabilizers. -/
def stabCheck : Bool :=
  (List.finRange orbitCount).all fun o => (icoStab o.val).all fun h => keq (icoApplyK h (slotK o.val)) (slotK o.val)

/-- The slots are closed under negation. -/
def symCheck : Bool :=
  (List.range 70).all fun i => (List.range 70).any fun j => keq (slotK j) (-(slotK i))

theorem orbitCheck_eq : orbitCheck = true := by decide +kernel
theorem stabCheck_eq : stabCheck = true := by decide +kernel
theorem symCheck_eq : symCheck = true := by decide +kernel

/-! ### The exact solid as an `IModel` -/

theorem dhScale_pos : (0 : ℝ) < (dhScale : ℝ) := by norm_num [dhScale]

theorem ico_smul_toEuc (n : Nat) (κ : ℝ) (v : Fin 3 → ℝ) :
    (ico n).toEuclideanLin (κ • toEuc v) = κ • toEuc (ico n *ᵥ v) := by
  rw [map_smul]
  congr 1

/-- The base point of orbit o. -/
noncomputable def dhV0 (o : Fin orbitCount) : ℝ³ := (dhScale : ℝ) • toEuc (kv (slotK o.val))

def dhBox (o : Fin orbitCount) : RatBox where
  lo r := dhScale * IcoQ.lo (slotK o.val r)
  hi r := dhScale * IcoQ.hi (slotK o.val r)

theorem dhV0_mem (o : Fin orbitCount) : (dhBox o).Mem (dhV0 o) := by
  intro r
  have hk := dhScale_pos
  have h1 := IcoQ.lo_le_val (slotK o.val r)
  have h2 := IcoQ.val_le_hi (slotK o.val r)
  simp only [dhBox, dhV0, toEuc, PiLp.smul_apply, smul_eq_mul, kv, PVec.kval]
  push_cast
  exact ⟨mul_le_mul_of_nonneg_left h1 hk.le, mul_le_mul_of_nonneg_left h2 hk.le⟩

theorem dhClose : closeCheck dhBox = true := by decide +kernel

theorem dhV0_fixed (o : Fin orbitCount) (h : Nat) (hh : h ∈ icoStab o.val) :
    (ico h).toEuclideanLin (dhV0 o) = dhV0 o := by
  have hc := stabCheck_eq
  simp only [stabCheck, List.all_eq_true, List.mem_finRange, forall_const] at hc
  have := eq_of_keq (hc o h hh)
  rw [dhV0, ico_smul_toEuc, ← kv_icoApplyK, this]

/-- The exact deltoidal hexecontahedron, scaled into the model frame. -/
noncomputable def dhIModel : IModel :=
  IModel.ofBoxes dhBox dhClose dhV0 dhV0_mem dhV0_fixed

theorem dhIModel_vertex (i : VertexIndex) :
    dhIModel.toC5.vertex i = (dhScale : ℝ) • toEuc (kv (slotK i.val)) := by
  have hc := orbitCheck_eq
  simp only [orbitCheck, List.all_eq_true, List.mem_range] at hc
  have hi := eq_of_keq (hc i.val (by simpa using i.isLt))
  rw [IModel.toC5_vertex, IModel.orbit]
  change (ico (vElem i.val)).toEuclideanLin (dhV0 (vOrbit i.val)) = _
  rw [dhV0, ico_smul_toEuc, ← kv_icoApplyK, hi]

/-- The vertex set: `dhScale` times the slots. -/
theorem dhIModel_verts :
    (dhIModel.toC5.verts : Set ℝ³) = {v | ∃ j < 70, v = (dhScale : ℝ) • toEuc (kv (slotK j))} := by
  ext v
  simp only [C5Model.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
    Set.mem_setOf_eq, dhIModel_vertex]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by simpa using i.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by simpa using hj⟩, rfl⟩

/-- … which is `dhScale · T` of McCooey's solid. -/
theorem dhIModel_verts_mcCooey :
    (dhIModel.toC5.verts : Set ℝ³) =
      (fun x => (dhScale : ℝ) • frameMat.toEuclideanLin x) '' deltoidalHexecontahedron := by
  have hm := mcCheck_eq
  have hs := slotMcCheck_eq
  simp only [mcCheck, slotMcCheck, List.all_eq_true, List.any_eq_true, List.mem_range] at hm hs
  have himg : ∀ g s k, frameMat.toEuclideanLin (mcPoint g s k) = toEuc (kv (frameApplyK (mcK g s k))) := by
    intro g s k
    rw [kv_frameApplyK, kv_mcK]
    simp [Matrix.toLpLin_apply, toEuc]
  rw [dhIModel_verts]
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_image, deltoidalHexecontahedron]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨⟨g, s, k⟩, -, hk⟩ := hs j hj
    refine ⟨mcPoint g s k, ⟨g, s, k, rfl⟩, ?_⟩
    rw [himg, eq_of_keq hk]
  · rintro ⟨_, ⟨g, s, k, rfl⟩, rfl⟩
    obtain ⟨j, hj, hk⟩ := hm (g, s, k) (mem_mcIndices g s k)
    exact ⟨j, hj, by rw [himg, eq_of_keq hk]⟩

/-! ### Central symmetry and the hull for cap certificates -/

theorem dhIModel_centrallySymmetric : dhIModel.CentrallySymmetric := by
  intro v hv
  have hc := symCheck_eq
  simp only [symCheck, List.all_eq_true, List.any_eq_true, List.mem_range] at hc
  rw [C5Model.polyhedron_hull] at hv ⊢
  have hneg : (-LinearMap.id : ℝ³ →ₗ[ℝ] ℝ³) '' (dhIModel.toC5.verts : Set ℝ³) = dhIModel.toC5.verts := by
    rw [dhIModel_verts]
    ext w
    simp only [Set.mem_image, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      obtain ⟨j', hj', hk⟩ := hc j hj
      refine ⟨j', hj', ?_⟩
      rw [eq_of_keq hk]
      ext r
      simp [toEuc, kv, PVec.kval]
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨j', hj', hk⟩ := hc j hj
      refine ⟨_, ⟨j', hj', rfl⟩, ?_⟩
      rw [eq_of_keq hk]
      ext r
      simp [toEuc, kv, PVec.kval]
  have := Set.mem_image_of_mem (-LinearMap.id : ℝ³ →ₗ[ℝ] ℝ³) hv
  rw [LinearMap.image_convexHull, hneg] at this
  simpa using this

/-- The same vertex set as the slots (natively checked for a cap certificate). -/
def sameSlots (L : List KVec) : Bool :=
  L.all (fun v => (List.range 70).any fun j => keq v (slotK j)) &&
    (List.range 70).all fun j => L.any fun v => keq v (slotK j)

theorem dhHull_eq (L : List KVec) (hL : sameSlots L = true) :
    dhIModel.toC5.polyhedron.hull =
      convexHull ℝ {v | ∃ vj ∈ L.map kv, v = (dhScale : ℝ) • toEuc vj} := by
  rw [C5Model.polyhedron_hull, dhIModel_verts]
  simp only [sameSlots, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at hL
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨w, hw, hk⟩ := hL.2 j hj
    exact ⟨kv w, ⟨w, hw, rfl⟩, by rw [eq_of_keq hk]⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨j, hj, hk⟩ := hL.1 w hw
    exact ⟨j, hj, by rw [eq_of_keq hk]⟩

/-! ### Main theorem -/

/-- If the exact solid's model is not Rupert, no deltoidal hexecontahedron is. -/
theorem deltoidalHexecontahedron_not_rupert (h : ¬ IsRupert dhIModel.toC5.verts) :
    ∀ V : Finset ℝ³, IsDeltoidalHexecontahedron V → ¬ IsRupert V := by
  rintro V ⟨c, s, M, hs, hM, hV⟩ hr
  apply h
  -- dhIModel's vertices are V under x ↦ dhScale T s⁻¹ Mᵀ (x − c), a similarity.
  have hMt : Mᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    simpa using (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hM
  have hMM : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
  have hTM : frameMat * Mᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ frameMat_orthogonal hMt
  have hk : (0 : ℝ) < (dhScale : ℝ) * s⁻¹ := mul_pos dhScale_pos (inv_pos.mpr hs)
  have hsim := isRupert_image_similarity
    (-(((dhScale : ℝ) * s⁻¹) • (frameMat * Mᵀ).toEuclideanLin c)) _ hk _ hTM _ hr
  convert hsim using 1
  apply Finset.coe_injective
  rw [Finset.coe_image, hV, dhIModel_verts_mcCooey, Set.image_image]
  congr 1
  funext x
  have hx : (frameMat * Mᵀ).toEuclideanLin (M.toEuclideanLin x) = frameMat.toEuclideanLin x := by
    rw [← IModel.toEuclideanLin_mul, Matrix.mul_assoc, hMM, Matrix.mul_one]
  simp only [map_add, map_smul, hx, smul_add, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
  abel

end Noperthedron.PentagonalHexecontahedron.DH
