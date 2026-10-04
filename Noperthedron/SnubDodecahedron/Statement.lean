module

public import Noperthedron.SnubDodecahedron.WikipediaSnub
public import Noperthedron.SnubDodecahedron.PolarDual
public import Noperthedron.SnubDodecahedron.PHStatementData

@[expose] public section

/-!
# The pentagonal hexecontahedron

The pentagonal hexecontahedron is the polar dual of the snub dodecahedron.
`pentagonalHexecontahedron` is the set of poles of the facet planes of
Wikipedia's snub dodecahedron (`facetPoles`, PolarDual.lean): the points y
with ⟪x, y⟫ ≤ 1 for every vertex x, with equality at three affinely
independent vertices. A polyhedron is *a* pentagonal hexecontahedron
(`IsPentagonalHexecontahedron`) when its vertices are the image of that set
under a similarity: a rotation or reflection, a positive scaling and a
translation. Both mirror images are included; the polar dual with respect to
any sphere about the center (e.g. the midsphere of the Catalan solid) is
such an image.

The proof that this set is exactly 92 points, the I-orbits of three poles
`basePole o`, uses the symmetry group of the snub (`wiki g`, 60 rotations,
transitive on its vertices) and decided interval arithmetic (ξ to 10⁻²⁴):
- every facet pole has a vertex at level 1, which a rotation moves to p; then
  for each pair (S_j p, S_k p) of other vertices (`pairCert`), either two
  vertices lie strictly on both sides of the plane through the three
  (`not_two_sided`), or the three lie on a known face and the pole is a
  rotated `basePole` (`eq_of_level`);
- each `basePole` is a facet pole: the other vertices are strictly below
  its plane (intervals), and the pentagon's five vertices are exactly
  coplanar (an orbit of M₁, the rotation about (0, 1, φ)).
The poles, rotated into the 5-fold frame (`snubFrame`) and scaled
(`phScale`), are an `IModel` (`phIModel`), which the certificates cover.

The same solid is cc-lib's PentagonalHexecontahedron() (McCooey's
coordinates), checked numerically (nopert229's ph_crosscheck.py): up to
similarity they agree to 4·10⁻⁴⁰, as mirror images.
-/

namespace Noperthedron.SnubDodecahedron

open IcoZ
open scoped RealInnerProductSpace Matrix

theorem getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem getD_eq_get {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The pentagonal hexecontahedron: the poles of the facet planes of Wikipedia's
snub dodecahedron (its polar dual). -/
def pentagonalHexecontahedron : Set ℝ³ := facetPoles (snubDodecahedron : Set ℝ³)

/-- A pentagonal hexecontahedron: the image of `pentagonalHexecontahedron` under a
similarity (an orthogonal map, possibly a reflection, a positive scaling and a
translation). -/
def IsPentagonalHexecontahedron (V : Finset ℝ³) : Prop :=
  ∃ (c : ℝ³) (s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ), 0 < s ∧
    M ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧
    (V : Set ℝ³) = (fun x => c + s • M.toEuclideanLin x) '' pentagonalHexecontahedron

/-! ### Wikipedia's group: closure, inverses, orthogonality -/

def wikiInv (g : Nat) : Nat := wikiInvIndex.getD g 0

/-- Decided over K: each element's inverse is its transpose, and it is orthogonal. -/
def wikiGroupCheck : Bool :=
  (List.range 60).all fun g =>
    decide (wikiInv g < 60) && decide (wikiEntry (wikiInv g) = M3.transpose (wikiEntry g)) &&
      decide (M3.mul8 (M3.transpose (wikiEntry g)) (wikiEntry g) = M3.scalar 3200)

theorem wikiGroupCheck_eq : wikiGroupCheck = true := by decide +kernel

theorem wiki_zero : wiki 0 = 1 := by
  have hc := wikiCheck_eq
  simp only [wikiCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [wiki, hc.1.1.1.1, M3.toMatrix_scalar, smul_smul]
  norm_num

theorem wiki_transpose_mul {g : Nat} (hg : g < 60) : (wiki g)ᵀ * wiki g = 1 := by
  have hc := wikiGroupCheck_eq
  simp only [wikiGroupCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  have h' := congrArg M3.toMatrix (hc g hg).2
  rw [M3.toMatrix_mul8, M3.toMatrix_transpose, M3.toMatrix_scalar] at h'
  rw [wiki, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have := congrArg (fun M => (1 / 3200 : ℝ) • M) h'
  simp only [smul_smul] at this
  norm_num at this ⊢
  exact this

theorem wiki_inv {g : Nat} (hg : g < 60) : wikiInv g < 60 ∧ wiki (wikiInv g) = (wiki g)ᵀ := by
  have hc := wikiGroupCheck_eq
  simp only [wikiGroupCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  refine ⟨(hc g hg).1.1, ?_⟩
  rw [wiki, wiki, (hc g hg).1.2, M3.toMatrix_transpose, Matrix.transpose_smul]

theorem wiki_mul_transpose {g : Nat} (hg : g < 60) : wiki g * (wiki g)ᵀ = 1 :=
  Matrix.mul_eq_one_comm.mp (wiki_transpose_mul hg)

theorem wiki_mul_of_mul8' {a b c : Nat}
    (h : M3.mul8 (wikiEntry a) (wikiEntry b) = M3.scale 160 (wikiEntry c)) :
    wiki a * wiki b = wiki c := by
  have h' := congrArg M3.toMatrix h
  rw [M3.toMatrix_mul8, M3.toMatrix_scale] at h'
  have hab : (wikiEntry a).toMatrix * (wikiEntry b).toMatrix =
      (20 : ℝ) • (wikiEntry c).toMatrix := by
    have := congrArg (fun M => (1 / 8 : ℝ) • M) h'
    simp only [smul_smul] at this
    norm_num at this
    exact this
  rw [wiki, wiki, wiki, Matrix.smul_mul, Matrix.mul_smul, hab, smul_smul, smul_smul]
  norm_num

/-- Closure of Wikipedia's 60 matrices under multiplication (from the BFS
parents and left multiplication by the generators). -/
theorem exists_wiki_mul (g h : Nat) (hg : g < 60) (hh : h < 60) :
    ∃ k < 60, wiki g * wiki h = wiki k := by
  have hc := wikiCheck_eq
  simp only [wikiCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨⟨-, hbfs⟩, hleft⟩ := hc
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    rcases Nat.eq_zero_or_pos g with rfl | hpos
    · exact ⟨h, hh, by rw [wiki_zero, Matrix.one_mul]⟩
    · obtain ⟨i, rfl⟩ : ∃ i, g = i + 1 := ⟨g - 1, by omega⟩
      obtain ⟨⟨hp, hgen⟩, hmul⟩ := hbfs i (by omega)
      have hstep := wiki_mul_of_mul8 hmul
      obtain ⟨k, hk, hpk⟩ := ih (wikiParent (i + 1)) hp (by omega)
      obtain ⟨hlt, hl⟩ := hleft k hk (wikiGenOf (i + 1)) hgen
      refine ⟨wikiLeft (wikiGenOf (i + 1)) k, hlt, ?_⟩
      rw [← hstep, Matrix.mul_assoc, hpk, ← wiki_mul_of_mul8 hl]

/-! ### The snub's vertices -/

/-- Vertex g of the snub: S_g p. -/
noncomputable def snubV (g : Nat) : ℝ³ := (wiki g).toEuclideanLin snubP

theorem snubV_zero : snubV 0 = snubP := by simp [snubV, wiki_zero]

theorem mem_snub_iff (x : ℝ³) : x ∈ (snubDodecahedron : Set ℝ³) ↔ ∃ g < 60, x = snubV g := by
  simp only [snubDodecahedron, Finset.coe_image, Finset.coe_range, Set.mem_image,
    Set.mem_Iio, snubV]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

theorem wiki_snubV {g h : Nat} (hg : g < 60) (hh : h < 60) :
    ∃ k < 60, (wiki g).toEuclideanLin (snubV h) = snubV k := by
  obtain ⟨k, hk, hmul⟩ := exists_wiki_mul g h hg hh
  exact ⟨k, hk, by rw [snubV, snubV, ← IModel.toEuclideanLin_mul, hmul]⟩

theorem wiki_mem_snub {g : Nat} (hg : g < 60) {x : ℝ³} (hx : x ∈ (snubDodecahedron : Set ℝ³)) :
    (wiki g).toEuclideanLin x ∈ (snubDodecahedron : Set ℝ³) := by
  obtain ⟨h, hh, rfl⟩ := (mem_snub_iff x).mp hx
  obtain ⟨k, hk, he⟩ := wiki_snubV hg hh
  exact (mem_snub_iff _).mpr ⟨k, hk, he⟩

theorem wikiT_mem_snub {g : Nat} (hg : g < 60) {x : ℝ³} (hx : x ∈ (snubDodecahedron : Set ℝ³)) :
    (wiki g)ᵀ.toEuclideanLin x ∈ (snubDodecahedron : Set ℝ³) := by
  obtain ⟨hlt, hinv⟩ := wiki_inv hg
  rw [← hinv]
  exact wiki_mem_snub hlt hx

theorem wiki_facetPoles {g : Nat} (hg : g < 60) {y : ℝ³} (hy : y ∈ pentagonalHexecontahedron) :
    (wiki g).toEuclideanLin y ∈ pentagonalHexecontahedron :=
  facetPoles_map (wiki_transpose_mul hg) (fun _ hx => wiki_mem_snub hg hx)
    (fun _ hx => wikiT_mem_snub hg hx) hy

theorem wiki_inner {g : Nat} (hg : g < 60) (x y : ℝ³) :
    ⟪(wiki g).toEuclideanLin x, (wiki g).toEuclideanLin y⟫ = ⟪x, y⟫ := by
  rw [inner_toEuclideanLin, ← IModel.toEuclideanLin_mul, wiki_transpose_mul hg]
  simp

/-! ### Rational boxes around the vertices -/

def xiWLoSq : ℚ := xiWLo ^ 2
def xiWHiSq : ℚ := xiWHi ^ 2

/-- A box around p (its coordinates are (A + B ξ + C ξ²)/20 over ℚ(√5)). -/
def pBox : RatBox where
  lo r := (IcoZ.lo (snubPA r) +
    mulLo (IcoZ.lo (snubPB r)) (IcoZ.hi (snubPB r)) xiWLo xiWHi +
    mulLo (IcoZ.lo (snubPC r)) (IcoZ.hi (snubPC r)) xiWLoSq xiWHiSq) / 20
  hi r := (IcoZ.hi (snubPA r) +
    mulHi (IcoZ.lo (snubPB r)) (IcoZ.hi (snubPB r)) xiWLo xiWHi +
    mulHi (IcoZ.lo (snubPC r)) (IcoZ.hi (snubPC r)) xiWLoSq xiWHiSq) / 20

theorem snubP_mem : pBox.Mem snubP := by
  intro r
  obtain ⟨hxlo, hxhi⟩ := snubXiW_bounds
  have hxpos := snubXiW_pos
  have hxi : ((xiWLo : ℚ) : ℝ) ≤ snubXiW ∧ snubXiW ≤ ((xiWHi : ℚ) : ℝ) := ⟨hxlo, hxhi⟩
  have hxlo0 : (0 : ℝ) ≤ (xiWLo : ℝ) := by unfold xiWLo; positivity
  have hxi2 : ((xiWLoSq : ℚ) : ℝ) ≤ snubXiW ^ 2 ∧ snubXiW ^ 2 ≤ ((xiWHiSq : ℚ) : ℝ) := by
    simp only [xiWLoSq, xiWHiSq, Rat.cast_pow]
    exact ⟨pow_le_pow_left₀ hxlo0 hxlo 2, pow_le_pow_left₀ hxpos.le hxhi 2⟩
  have hencl : ∀ x : IcoZ, ((IcoZ.lo x : ℚ) : ℝ) ≤ IcoZ.val x ∧ IcoZ.val x ≤ ((IcoZ.hi x : ℚ) : ℝ) :=
    fun x => ⟨IcoZ.lo_le_val x, IcoZ.val_le_hi x⟩
  have hB := mulLo_le (hencl (snubPB r)) hxi
  have hB' := le_mulHi (hencl (snubPB r)) hxi
  have hC := mulLo_le (hencl (snubPC r)) hxi2
  have hC' := le_mulHi (hencl (snubPC r)) hxi2
  have hA := hencl (snubPA r)
  rw [snubP_eq]
  simp only [pBox]
  push_cast
  constructor <;> linarith [hA.1, hA.2]

/-- Enclosure of `((A/20) *ᵥ v) r` for v in B, for any K-matrix A (times 20). -/
def imageLoK (A : M3) (B : RatBox) (r : Fin 3) : ℚ :=
  ∑ c, mulLo (IcoZ.lo (A.entry r c) / 20) (IcoZ.hi (A.entry r c) / 20) (B.lo c) (B.hi c)

def imageHiK (A : M3) (B : RatBox) (r : Fin 3) : ℚ :=
  ∑ c, mulHi (IcoZ.lo (A.entry r c) / 20) (IcoZ.hi (A.entry r c) / 20) (B.lo c) (B.hi c)

def imageBoxK (A : M3) (B : RatBox) : RatBox := ⟨imageLoK A B, imageHiK A B⟩

theorem imageK_mem (A : M3) (B : RatBox) {v : ℝ³} (hv : B.Mem v) :
    (imageBoxK A B).Mem (((1 / 20 : ℝ) • A.toMatrix).toEuclideanLin v) := by
  intro r
  have hentry : ∀ c, (IcoZ.lo (A.entry r c) / 20 : ℚ) ≤ (((1 / 20 : ℝ) • A.toMatrix) r c : ℝ) ∧
      (((1 / 20 : ℝ) • A.toMatrix) r c : ℝ) ≤ ((IcoZ.hi (A.entry r c) / 20 : ℚ) : ℝ) := by
    intro c
    have h1 := IcoZ.lo_le_val (A.entry r c)
    have h2 := IcoZ.val_le_hi (A.entry r c)
    have hval : ((1 / 20 : ℝ) • A.toMatrix) r c = IcoZ.val (A.entry r c) / 20 := by
      simp [M3.toMatrix]
      ring
    rw [hval]
    push_cast
    constructor <;> linarith
  have happly : (((1 / 20 : ℝ) • A.toMatrix).toEuclideanLin v) r =
      ∑ c, ((1 / 20 : ℝ) • A.toMatrix) r c * v c := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [happly]
  constructor
  · simp only [imageBoxK, imageLoK]
    push_cast
    exact Finset.sum_le_sum fun c _ => mulLo_le (hentry c) (hv c)
  · simp only [imageBoxK, imageHiK]
    push_cast
    exact Finset.sum_le_sum fun c _ => le_mulHi (hentry c) (hv c)

/-- The generated box around vertex g (endpoints `snubBoxLoZ`, `snubBoxHiZ` / 2^64). -/
def boxLoZ (g : Nat) (r : Fin 3) : Int := (snubBoxLoZ.getD g []).getD r.val 0
def boxHiZ (g : Nat) (r : Fin 3) : Int := (snubBoxHiZ.getD g []).getD r.val 0

def vBox (g : Nat) : RatBox where
  lo r := (boxLoZ g r : ℚ) / 2 ^ 64
  hi r := (boxHiZ g r : ℚ) / 2 ^ 64

def vBoxCheck : Bool :=
  (List.range 60).all fun g => (List.finRange 3).all fun r =>
    decide ((vBox g).lo r ≤ imageLoK (wikiEntry g) pBox r) &&
      decide (imageHiK (wikiEntry g) pBox r ≤ (vBox g).hi r)

theorem vBoxCheck_eq : vBoxCheck = true := by decide +kernel

theorem snubV_mem {g : Nat} (hg : g < 60) : (vBox g).Mem (snubV g) := by
  have hc := vBoxCheck_eq
  simp only [vBoxCheck, List.all_eq_true, List.mem_range, List.mem_finRange,
    forall_true_left, Bool.and_eq_true, decide_eq_true_eq] at hc
  intro r
  have hm := imageK_mem (wikiEntry g) pBox snubP_mem r
  obtain ⟨h1, h2⟩ := hc g hg r
  have h1' : ((vBox g).lo r : ℝ) ≤ (imageLoK (wikiEntry g) pBox r : ℝ) := by exact_mod_cast h1
  have h2' : (imageHiK (wikiEntry g) pBox r : ℝ) ≤ ((vBox g).hi r : ℝ) := by exact_mod_cast h2
  simp only [imageBoxK] at hm
  exact ⟨h1'.trans hm.1, hm.2.trans h2'⟩

/-! ### Interval arithmetic -/

/-- A closed rational interval. -/
structure Iv where
  lo : ℚ
  hi : ℚ

def Iv.Mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

def Iv.add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩
def Iv.sub (I J : Iv) : Iv := ⟨I.lo - J.hi, I.hi - J.lo⟩
def Iv.mul (I J : Iv) : Iv := ⟨mulLo I.lo I.hi J.lo J.hi, mulHi I.lo I.hi J.lo J.hi⟩

theorem Iv.add_mem {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.add J).Mem (x + y) := by
  simp only [Iv.Mem, Iv.add] at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem Iv.sub_mem {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.sub J).Mem (x - y) := by
  simp only [Iv.Mem, Iv.sub] at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem Iv.mul_mem {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.mul J).Mem (x * y) :=
  ⟨mulLo_le hx hy, le_mulHi hx hy⟩

/-- The reciprocal of an interval not containing 0. -/
def Iv.inv (I : Iv) : Iv := ⟨1 / I.hi, 1 / I.lo⟩

theorem Iv.inv_mem {I : Iv} {x : ℝ} (h0 : 0 < I.lo ∨ I.hi < 0) (hx : I.Mem x) :
    I.inv.Mem x⁻¹ := by
  obtain ⟨hl, hh⟩ := hx
  simp only [Iv.Mem, Iv.inv]
  push_cast
  rcases h0 with h | h
  · have hl' : (0 : ℝ) < I.lo := by exact_mod_cast h
    have hx0 : 0 < x := lt_of_lt_of_le hl' hl
    rw [one_div, one_div]
    exact ⟨inv_anti₀ hx0 hh, inv_anti₀ hl' hl⟩
  · have hh' : (I.hi : ℝ) < 0 := by exact_mod_cast h
    have hx0 : x < 0 := lt_of_le_of_lt hh hh'
    rw [one_div, one_div]
    exact ⟨(inv_le_inv_of_neg hh' hx0).mpr hh, (inv_le_inv_of_neg hx0 (by linarith)).mpr hl⟩

/-- Coordinate intervals of a box. -/
def RatBox.iv (B : RatBox) (r : Fin 3) : Iv := ⟨B.lo r, B.hi r⟩

/-- `det3` over intervals. -/
def det3I (u v w : Fin 3 → Iv) : Iv :=
  ((u 0).mul (((v 1).mul (w 2)).sub ((v 2).mul (w 1)))).sub
    ((u 1).mul (((v 0).mul (w 2)).sub ((v 2).mul (w 0)))) |>.add
    ((u 2).mul (((v 0).mul (w 1)).sub ((v 1).mul (w 0))))

theorem det3I_mem {u v w : Fin 3 → Iv} {a b c : ℝ³} (ha : ∀ r, (u r).Mem (a r))
    (hb : ∀ r, (v r).Mem (b r)) (hc : ∀ r, (w r).Mem (c r)) : (det3I u v w).Mem (det3 a b c) := by
  unfold det3I det3
  exact Iv.add_mem (Iv.sub_mem
    (Iv.mul_mem (ha 0) (Iv.sub_mem (Iv.mul_mem (hb 1) (hc 2)) (Iv.mul_mem (hb 2) (hc 1))))
    (Iv.mul_mem (ha 1) (Iv.sub_mem (Iv.mul_mem (hb 0) (hc 2)) (Iv.mul_mem (hb 2) (hc 0)))))
    (Iv.mul_mem (ha 2) (Iv.sub_mem (Iv.mul_mem (hb 0) (hc 1)) (Iv.mul_mem (hb 1) (hc 0))))

/-- Interval coordinates of vertex g, and of the difference of two vertices. -/
def vIv (g : Nat) (r : Fin 3) : Iv := (vBox g).iv r
def dIv (g h : Nat) (r : Fin 3) : Iv := (vIv g r).sub (vIv h r)

theorem vIv_mem {g : Nat} (hg : g < 60) (r : Fin 3) : (vIv g r).Mem (snubV g r) :=
  snubV_mem hg r

theorem dIv_mem {g h : Nat} (hg : g < 60) (hh : h < 60) (r : Fin 3) :
    (dIv g h r).Mem ((snubV g - snubV h) r) := by
  rw [PiLp.sub_apply]
  exact Iv.sub_mem (vIv_mem hg r) (vIv_mem hh r)

/-- det(S_b − S_a, S_c − S_a, S_x − S_a), enclosed. -/
def sideIv (a b c x : Nat) : Iv := det3I (dIv b a) (dIv c a) (dIv x a)

theorem sideIv_mem {a b c x : Nat} (ha : a < 60) (hb : b < 60) (hc : c < 60) (hx : x < 60) :
    (sideIv a b c x).Mem (det3 (snubV b - snubV a) (snubV c - snubV a) (snubV x - snubV a)) :=
  det3I_mem (dIv_mem hb ha) (dIv_mem hc ha) (dIv_mem hx ha)

/-- det(S_a, S_b, S_c), enclosed. -/
def detIv (a b c : Nat) : Iv := det3I (vIv a) (vIv b) (vIv c)

theorem detIv_mem {a b c : Nat} (ha : a < 60) (hb : b < 60) (hc : c < 60) :
    (detIv a b c).Mem (det3 (snubV a) (snubV b) (snubV c)) :=
  det3I_mem (vIv_mem ha) (vIv_mem hb) (vIv_mem hc)

def Iv.ExcludesZero (I : Iv) : Prop := 0 < I.lo ∨ I.hi < 0

instance (I : Iv) : Decidable I.ExcludesZero := by unfold Iv.ExcludesZero; infer_instance

theorem Iv.ne_zero_of {I : Iv} {x : ℝ} (h : I.ExcludesZero) (hx : I.Mem x) : x ≠ 0 := by
  obtain ⟨hl, hh⟩ := hx
  rcases h with h | h
  · have : (0 : ℝ) < I.lo := by exact_mod_cast h
    linarith
  · have : (I.hi : ℝ) < 0 := by exact_mod_cast h
    linarith

/-! ### Integer interval arithmetic (scaled by 2^64), for the pair checks

The kernel evaluates integer products much faster than rational ones (no
gcd). Only signs matter for the pair certificates, so these determinants are
computed on the vertex boxes times 2^64, in integers. -/

/-- A closed integer interval. -/
structure IvZ where
  lo : Int
  hi : Int

def IvZ.Mem (I : IvZ) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

def IvZ.add (I J : IvZ) : IvZ := ⟨I.lo + J.lo, I.hi + J.hi⟩
def IvZ.sub (I J : IvZ) : IvZ := ⟨I.lo - J.hi, I.hi - J.lo⟩
def IvZ.mul (I J : IvZ) : IvZ :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

theorem IvZ.add_mem {I J : IvZ} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.add J).Mem (x + y) := by
  simp only [IvZ.Mem, IvZ.add] at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem IvZ.sub_mem {I J : IvZ} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.sub J).Mem (x - y) := by
  simp only [IvZ.Mem, IvZ.sub] at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem IvZ.mul_mem {I J : IvZ} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.mul J).Mem (x * y) := by
  have h1 := mulLo_le (a := (I.lo : ℚ)) (b := (I.hi : ℚ)) (c := (J.lo : ℚ)) (d := (J.hi : ℚ))
    (x := x) (y := y) (by exact_mod_cast hx) (by exact_mod_cast hy)
  have h2 := le_mulHi (a := (I.lo : ℚ)) (b := (I.hi : ℚ)) (c := (J.lo : ℚ)) (d := (J.hi : ℚ))
    (x := x) (y := y) (by exact_mod_cast hx) (by exact_mod_cast hy)
  simp only [mulLo, mulHi] at h1 h2
  simp only [IvZ.Mem, IvZ.mul]
  push_cast at h1 h2 ⊢
  exact ⟨h1, h2⟩

def det3Z (u v w : Fin 3 → IvZ) : IvZ :=
  ((u 0).mul (((v 1).mul (w 2)).sub ((v 2).mul (w 1)))).sub
    ((u 1).mul (((v 0).mul (w 2)).sub ((v 2).mul (w 0)))) |>.add
    ((u 2).mul (((v 0).mul (w 1)).sub ((v 1).mul (w 0))))

theorem det3Z_mem {u v w : Fin 3 → IvZ} {a b c : ℝ³} (ha : ∀ r, (u r).Mem (a r))
    (hb : ∀ r, (v r).Mem (b r)) (hc : ∀ r, (w r).Mem (c r)) : (det3Z u v w).Mem (det3 a b c) := by
  unfold det3Z det3
  exact IvZ.add_mem (IvZ.sub_mem
    (IvZ.mul_mem (ha 0) (IvZ.sub_mem (IvZ.mul_mem (hb 1) (hc 2)) (IvZ.mul_mem (hb 2) (hc 1))))
    (IvZ.mul_mem (ha 1) (IvZ.sub_mem (IvZ.mul_mem (hb 0) (hc 2)) (IvZ.mul_mem (hb 2) (hc 0)))))
    (IvZ.mul_mem (ha 2) (IvZ.sub_mem (IvZ.mul_mem (hb 0) (hc 1)) (IvZ.mul_mem (hb 1) (hc 0))))

/-- Vertex g's coordinates times 2^64, and differences. -/
def vZ (g : Nat) (r : Fin 3) : IvZ := ⟨boxLoZ g r, boxHiZ g r⟩
def dZ (g h : Nat) (r : Fin 3) : IvZ := (vZ g r).sub (vZ h r)

/-- 2^64 · v. -/
noncomputable def scale64 (v : ℝ³) : ℝ³ := ((2 : ℝ) ^ 64) • v

theorem vZ_mem {g : Nat} (hg : g < 60) (r : Fin 3) : (vZ g r).Mem (scale64 (snubV g) r) := by
  obtain ⟨h1, h2⟩ := snubV_mem hg r
  simp only [vBox] at h1 h2
  push_cast at h1 h2
  simp only [IvZ.Mem, vZ, scale64, PiLp.smul_apply, smul_eq_mul]
  have hp : (0 : ℝ) < 2 ^ 64 := by positivity
  constructor
  · rw [div_le_iff₀ hp] at h1; linarith
  · rw [le_div_iff₀ hp] at h2; linarith

theorem dZ_mem {g h : Nat} (hg : g < 60) (hh : h < 60) (r : Fin 3) :
    (dZ g h r).Mem (scale64 (snubV g - snubV h) r) := by
  have : scale64 (snubV g - snubV h) r = scale64 (snubV g) r - scale64 (snubV h) r := by
    simp [scale64, mul_sub]
  rw [this]
  exact IvZ.sub_mem (vZ_mem hg r) (vZ_mem hh r)

theorem det3_scale64 (a b c : ℝ³) : det3 (scale64 a) (scale64 b) (scale64 c) = (2 ^ 64) ^ 3 * det3 a b c := by
  simp only [det3, scale64, PiLp.smul_apply, smul_eq_mul]
  ring

/-- det(S_b − S_a, S_c − S_a, S_x − S_a) times 2^192, enclosed. -/
def sideZ (a b c x : Nat) : IvZ := det3Z (dZ b a) (dZ c a) (dZ x a)

theorem sideZ_mem {a b c x : Nat} (ha : a < 60) (hb : b < 60) (hc : c < 60) (hx : x < 60) :
    (sideZ a b c x).Mem ((2 ^ 64) ^ 3 *
      det3 (snubV b - snubV a) (snubV c - snubV a) (snubV x - snubV a)) := by
  rw [← det3_scale64]
  exact det3Z_mem (dZ_mem hb ha) (dZ_mem hc ha) (dZ_mem hx ha)

/-- det(S_a, S_b, S_c) times 2^192, enclosed. -/
def detZ (a b c : Nat) : IvZ := det3Z (vZ a) (vZ b) (vZ c)

theorem detZ_mem {a b c : Nat} (ha : a < 60) (hb : b < 60) (hc : c < 60) :
    (detZ a b c).Mem ((2 ^ 64) ^ 3 * det3 (snubV a) (snubV b) (snubV c)) := by
  rw [← det3_scale64]
  exact det3Z_mem (vZ_mem ha) (vZ_mem hb) (vZ_mem hc)

theorem pos_of_scaled {x : ℝ} {l : Int} (hl : 0 < l) (h : (l : ℝ) ≤ (2 ^ 64) ^ 3 * x) : 0 < x := by
  have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hp : (0 : ℝ) < (2 ^ 64) ^ 3 := by positivity
  by_contra hx
  push_neg at hx
  nlinarith

theorem neg_of_scaled {x : ℝ} {u : Int} (hu : u < 0) (h : (2 ^ 64) ^ 3 * x ≤ (u : ℝ)) : x < 0 := by
  have : (u : ℝ) < 0 := by exact_mod_cast hu
  have hp : (0 : ℝ) < (2 ^ 64) ^ 3 := by positivity
  by_contra hx
  push_neg at hx
  nlinarith

/-! ### The base faces and their poles -/

def baseFaceOf (o : Nat) : List Nat := baseFace.getD o []
def baseStabOf (o : Nat) : List Nat := baseStab.getD o []
def fv (o i : Nat) : Nat := (baseFaceOf o).getD i 0

/-- The pole of base face o, through its first three vertices. -/
noncomputable def basePole (o : Nat) : ℝ³ := pole (snubV (fv o 0)) (snubV (fv o 1)) (snubV (fv o 2))

/-- M₁'s orbit of vertex 0 (the pentagon about (0, 1, φ)). -/
def m1Orbit : List Nat := [0, wikiLeft 0 0, wikiLeft 0 (wikiLeft 0 0),
  wikiLeft 0 (wikiLeft 0 (wikiLeft 0 0)), wikiLeft 0 (wikiLeft 0 (wikiLeft 0 (wikiLeft 0 0)))]

/-- Decided: each base face has vertices < 60, a nonzero determinant, and
every other vertex strictly on the side of its plane opposite to the
origin's (`sideIv` against `detIv`); a face with more than three vertices is
M₁'s orbit of vertex 0. -/
def baseCheck : Bool :=
  (List.range 3).all fun o =>
    ((baseFaceOf o).all (· < 60)) && decide (3 ≤ (baseFaceOf o).length) &&
      (decide ((baseFaceOf o).length = 3) || decide (baseFaceOf o = m1Orbit)) &&
      decide (detIv (fv o 0) (fv o 1) (fv o 2)).ExcludesZero &&
      (List.range 60).all fun m =>
        (baseFaceOf o).contains m ||
          (decide (0 < (detIv (fv o 0) (fv o 1) (fv o 2)).lo) &&
            decide ((sideIv (fv o 0) (fv o 1) (fv o 2) m).hi < 0)) ||
          (decide ((detIv (fv o 0) (fv o 1) (fv o 2)).hi < 0) &&
            decide (0 < (sideIv (fv o 0) (fv o 1) (fv o 2) m).lo))

theorem baseCheck_eq : baseCheck = true := by decide +kernel

theorem baseCheck_spec {o : Nat} (ho : o < 3) :
    (∀ m ∈ baseFaceOf o, m < 60) ∧ 3 ≤ (baseFaceOf o).length ∧
      ((baseFaceOf o).length = 3 ∨ baseFaceOf o = m1Orbit) ∧
      (detIv (fv o 0) (fv o 1) (fv o 2)).ExcludesZero ∧
      ∀ m < 60, m ∈ baseFaceOf o ∨
        (0 < (detIv (fv o 0) (fv o 1) (fv o 2)).lo ∧ (sideIv (fv o 0) (fv o 1) (fv o 2) m).hi < 0) ∨
        ((detIv (fv o 0) (fv o 1) (fv o 2)).hi < 0 ∧ 0 < (sideIv (fv o 0) (fv o 1) (fv o 2) m).lo) := by
  have hc := baseCheck_eq
  simp only [baseCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.contains_iff_mem] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc o ho
  refine ⟨h1, h2, h3, h4, fun m hm => ?_⟩
  rcases h5 m hm with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem fv_lt {o i : Nat} (ho : o < 3) (hi : i < 3) : fv o i < 60 := by
  obtain ⟨h1, h2, -⟩ := baseCheck_spec ho
  exact h1 _ (getD_mem (by omega))

theorem baseDet_ne {o : Nat} (ho : o < 3) :
    det3 (snubV (fv o 0)) (snubV (fv o 1)) (snubV (fv o 2)) ≠ 0 :=
  Iv.ne_zero_of (baseCheck_spec ho).2.2.2.1
    (detIv_mem (fv_lt ho (by norm_num)) (fv_lt ho (by norm_num)) (fv_lt ho (by norm_num)))

/-- The axis of M₁. -/
noncomputable def m1Axis : ℝ³ := WithLp.toLp 2 ![0, 1, goldenPhi]

theorem goldenPhi_sq : goldenPhi ^ 2 = goldenPhi + 1 := by
  unfold goldenPhi
  have := sqrt5_sq
  nlinarith

theorem snubM1_axis : snubM1.toEuclideanLin m1Axis = m1Axis := by
  have hne := goldenPhi_ne
  have hsq := goldenPhi_sq
  ext i
  fin_cases i <;>
    simp [snubM1, m1Axis, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp <;> nlinarith [hsq]

theorem wiki_one : wiki 1 = snubM1 := by
  have hc := wikiCheck_eq
  simp only [wikiCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [wiki, hc.1.1.1.2, wikiGen_real 0, if_pos rfl]

theorem wikiLeft_zero {g : Nat} (hg : g < 60) :
    wikiLeft 0 g < 60 ∧ wiki (wikiLeft 0 g) = snubM1 * wiki g := by
  have hc := wikiCheck_eq
  simp only [wikiCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨hlt, hmul⟩ := hc.2 g hg 0 (by norm_num)
  refine ⟨hlt, ?_⟩
  rw [← wiki_mul_of_mul8 hmul, wikiGen_real]
  simp

/-- ⟪k, S_m p⟫ = ⟪k, p⟫ along M₁'s orbit of p (k the axis). -/
theorem m1Axis_inner_orbit {m : Nat} (hm : m ∈ m1Orbit) : ⟪m1Axis, snubV m⟫ = ⟪m1Axis, snubP⟫ := by
  have hT : snubM1ᵀ.toEuclideanLin m1Axis = m1Axis := by
    have horth : snubM1ᵀ * snubM1 = 1 := by rw [← wiki_one]; exact wiki_transpose_mul (by norm_num)
    conv_lhs => rw [← snubM1_axis]
    rw [← IModel.toEuclideanLin_mul, horth]
    simp
  have step : ∀ g < 60, ⟪m1Axis, snubV (wikiLeft 0 g)⟫ = ⟪m1Axis, snubV g⟫ := by
    intro g hg
    rw [snubV, (wikiLeft_zero hg).2, IModel.toEuclideanLin_mul, inner_toEuclideanLin, hT]
    rfl
  have h0 : (0 : Nat) < 60 := by norm_num
  have l1 := wikiLeft_zero h0
  have l2 := wikiLeft_zero l1.1
  have l3 := wikiLeft_zero l2.1
  have l4 := wikiLeft_zero l3.1
  simp only [m1Orbit, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · rw [snubV_zero]
  · rw [step 0 h0, snubV_zero]
  · rw [step _ l1.1, step 0 h0, snubV_zero]
  · rw [step _ l2.1, step _ l1.1, step 0 h0, snubV_zero]
  · rw [step _ l3.1, step _ l2.1, step _ l1.1, step 0 h0, snubV_zero]

/-- Three vectors orthogonal to M₁'s axis have zero determinant. -/
theorem det3_eq_zero_of_perp {u v w : ℝ³} (hu : ⟪m1Axis, u⟫ = 0) (hv : ⟪m1Axis, v⟫ = 0)
    (hw : ⟪m1Axis, w⟫ = 0) : det3 u v w = 0 := by
  have key : det3 u v w * (1 : ℝ) = ⟪m1Axis, u⟫ * (v 2 * w 0 - v 0 * w 2) +
      ⟪m1Axis, v⟫ * (w 2 * u 0 - w 0 * u 2) + ⟪m1Axis, w⟫ * (u 2 * v 0 - u 0 * v 2) := by
    simp only [inner_eq3, m1Axis, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, det3]
    ring
  rw [hu, hv, hw] at key
  linarith

/-- Every vertex of a base face is on the plane of its pole. -/
theorem baseFace_level {o m : Nat} (ho : o < 3) (hm : m ∈ baseFaceOf o) :
    ⟪snubV m, basePole o⟫ = 1 := by
  unfold basePole
  obtain ⟨hlt, hlen, hshape, -, -⟩ := baseCheck_spec ho
  have hd := baseDet_ne ho
  obtain ⟨l0, l1, l2⟩ := pole_level hd
  have hidx : ∀ i < 3, ⟪snubV (fv o i), pole (snubV (fv o 0)) (snubV (fv o 1)) (snubV (fv o 2))⟫ = 1 := by
    intro i hi
    interval_cases i
    · exact l0
    · exact l1
    · exact l2
  rcases hshape with h3 | hpent
  · -- A triangle: m is one of its three vertices.
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have : fv o i = (baseFaceOf o)[i] := getD_eq_get hi
    rw [← this]
    exact hidx i (by omega)
  · -- The pentagon: its five vertices are coplanar (perpendicular to M₁'s axis).
    have hf : ∀ i < 3, fv o i ∈ m1Orbit := by
      intro i hi
      simp only [fv, hpent]
      interval_cases i <;> simp [m1Orbit]
    have hm' : m ∈ m1Orbit := hpent ▸ hm
    have hperp : ∀ g ∈ m1Orbit, ⟪m1Axis, snubV g - snubV (fv o 0)⟫ = 0 := by
      intro g hg
      rw [inner_sub_right, m1Axis_inner_orbit hg, m1Axis_inner_orbit (hf 0 (by norm_num)), sub_self]
    have hD : det3 (snubV (fv o 1) - snubV (fv o 0)) (snubV (fv o 2) - snubV (fv o 0))
        (snubV m - snubV (fv o 0)) = 0 :=
      det3_eq_zero_of_perp (hperp _ (hf 1 (by norm_num))) (hperp _ (hf 2 (by norm_num))) (hperp _ hm')
    have e := level_identity (x := snubV m) l0 l1 l2
    rw [hD] at e
    have := (mul_eq_zero.mp e).resolve_left hd
    linarith

/-- Each base pole is a facet pole. -/
theorem basePole_mem {o : Nat} (ho : o < 3) : basePole o ∈ pentagonalHexecontahedron := by
  have hlevel := fun m (hm : m ∈ baseFaceOf o) => baseFace_level ho hm
  unfold basePole at hlevel ⊢
  obtain ⟨hlt, hlen, -, -, hside⟩ := baseCheck_spec ho
  have hd := baseDet_ne ho
  obtain ⟨l0, l1, l2⟩ := pole_level hd
  have h0 := fv_lt ho (show 0 < 3 by norm_num)
  have h1 := fv_lt ho (show 1 < 3 by norm_num)
  have h2 := fv_lt ho (show 2 < 3 by norm_num)
  refine ⟨fun x hx => ?_, snubV (fv o 0), (mem_snub_iff _).mpr ⟨_, h0, rfl⟩,
    snubV (fv o 1), (mem_snub_iff _).mpr ⟨_, h1, rfl⟩,
    snubV (fv o 2), (mem_snub_iff _).mpr ⟨_, h2, rfl⟩, affineIndependent_of_det hd, l0, l1, l2⟩
  obtain ⟨m, hm, rfl⟩ := (mem_snub_iff x).mp hx
  have e := level_identity (x := snubV m) l0 l1 l2
  have hdm := detIv_mem h0 h1 h2
  have hsm := sideIv_mem h0 h1 h2 hm
  rcases hside m hm with hin | ⟨hdpos, hneg⟩ | ⟨hdneg, hpos⟩
  · exact (hlevel m hin).le
  · have : (0 : ℝ) < det3 (snubV (fv o 0)) (snubV (fv o 1)) (snubV (fv o 2)) :=
      lt_of_lt_of_le (by exact_mod_cast hdpos) hdm.1
    have : det3 (snubV (fv o 1) - snubV (fv o 0)) (snubV (fv o 2) - snubV (fv o 0))
        (snubV m - snubV (fv o 0)) < 0 := lt_of_le_of_lt hsm.2 (by exact_mod_cast hneg)
    nlinarith
  · have : det3 (snubV (fv o 0)) (snubV (fv o 1)) (snubV (fv o 2)) < 0 :=
      lt_of_le_of_lt hdm.2 (by exact_mod_cast hdneg)
    have : 0 < det3 (snubV (fv o 1) - snubV (fv o 0)) (snubV (fv o 2) - snubV (fv o 0))
        (snubV m - snubV (fv o 0)) := lt_of_lt_of_le (by exact_mod_cast hpos) hsm.1
    nlinarith

/-- Decided: each element of `baseStab o` maps the three defining vertices of
base face o into the face (so it fixes the pole). -/
def baseStabCheck : Bool :=
  (List.range 3).all fun o => (baseStabOf o).all fun τ =>
    decide (τ < 60) && (List.range 3).all fun i =>
      (baseFaceOf o).any fun m =>
        decide (M3.mul8 (wikiEntry (wikiInv τ)) (wikiEntry (fv o i)) = M3.scale 160 (wikiEntry m))

theorem baseStabCheck_eq : baseStabCheck = true := by decide +kernel

theorem baseStab_fix {o τ : Nat} (ho : o < 3) (hτ : τ ∈ baseStabOf o) :
    τ < 60 ∧ (wiki τ).toEuclideanLin (basePole o) = basePole o := by
  have hc := baseStabCheck_eq
  simp only [baseStabCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, List.any_eq_true] at hc
  obtain ⟨hlt, hmap⟩ := hc o ho τ hτ
  refine ⟨hlt, ?_⟩
  have hd := baseDet_ne ho
  obtain ⟨l0, l1, l2⟩ := pole_level hd
  obtain ⟨hinv, hinvT⟩ := wiki_inv hlt
  have hlev : ∀ i < 3, ⟪snubV (fv o i), (wiki τ).toEuclideanLin (basePole o)⟫ = 1 := by
    intro i hi
    obtain ⟨m, hm, hmul⟩ := hmap i hi
    rw [inner_toEuclideanLin, ← hinvT, snubV, ← IModel.toEuclideanLin_mul,
      wiki_mul_of_mul8' hmul]
    exact baseFace_level ho hm
  exact (eq_of_level hd l0 l1 l2 (hlev 0 (by norm_num)) (hlev 1 (by norm_num))
    (hlev 2 (by norm_num))).symm

/-! ### Every facet pole is a rotated base pole -/

def pairCertOf (j k : Nat) : List Nat := pairCert.getD (60 * j + k) []

def faceVertexOK (o h a m : Nat) : Bool :=
  (baseFaceOf o).contains m &&
    decide (M3.mul8 (wikiEntry (wikiInv h)) (wikiEntry a) = M3.scale 160 (wikiEntry m))

/-- The check of one pair's certificate `c`. -/
def pairOKc (j k : Nat) (c : List Nat) : Bool :=
  match c with
  | [0] => decide (j = 0) || decide (k = 0) || decide (k ≤ j)
  | [1, x₁, x₂] => decide (x₁ < 60) && decide (x₂ < 60) &&
      decide (0 < (sideZ 0 j k x₁).lo) && decide ((sideZ 0 j k x₂).hi < 0)
  | [2, o, h, m₀, m₁, m₂] => decide (o < 3) && decide (h < 60) &&
      faceVertexOK o h 0 m₀ && faceVertexOK o h j m₁ && faceVertexOK o h k m₂ &&
      (decide (0 < (detZ 0 j k).lo) || decide ((detZ 0 j k).hi < 0))
  | _ => false

def pairOK (j k : Nat) : Bool := pairOKc j k (pairCertOf j k)

/-- Walks the certificate list once (entry n is the pair (n / 60, n % 60)). -/
def pairCheckFrom : List (List Nat) → Nat → Bool
  | [], n => decide (n = 3600)
  | c :: cs, n => pairOKc (n / 60) (n % 60) c && pairCheckFrom cs (n + 1)

def pairCheck : Bool := pairCheckFrom pairCert 0

theorem pairCheck_eq : pairCheck = true := by decide +kernel

theorem pairCheckFrom_spec : ∀ (l : List (List Nat)) (n : Nat), pairCheckFrom l n = true →
    n + l.length = 3600 ∧ ∀ i < l.length, pairOKc ((n + i) / 60) ((n + i) % 60) (l.getD i []) = true
  | [], n, h => by simp [pairCheckFrom] at h; simp [h]
  | c :: cs, n, h => by
    simp only [pairCheckFrom, Bool.and_eq_true] at h
    obtain ⟨hc, hcs⟩ := pairCheckFrom_spec cs (n + 1) h.2
    refine ⟨by simp; omega, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using h.1
    · have := hcs i (by simpa using hi)
      simpa [show n + (i + 1) = n + 1 + i by omega] using this

theorem pairOK_of {j k : Nat} (hj : j < 60) (hk : k < 60) : pairOK j k = true := by
  obtain ⟨hlen, hall⟩ := pairCheckFrom_spec pairCert 0 pairCheck_eq
  have := hall (60 * j + k) (by omega)
  simp only [zero_add] at this
  rw [show (60 * j + k) / 60 = j by omega, show (60 * j + k) % 60 = k by omega] at this
  exact this

theorem faceVertexOK_spec {o h a m : Nat} (ho : o < 3) (hh : h < 60) (ha : a < 60)
    (hok : faceVertexOK o h a m = true) :
    ⟪snubV a, (wiki h).toEuclideanLin (basePole o)⟫ = 1 := by
  simp only [faceVertexOK, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hok
  obtain ⟨hinv, hinvT⟩ := wiki_inv hh
  rw [inner_toEuclideanLin, ← hinvT, snubV, ← IModel.toEuclideanLin_mul,
    wiki_mul_of_mul8' hok.2]
  exact baseFace_level ho hok.1

/-- A facet pole with vertex 0 and vertices j, k at level 1 is a rotated base pole. -/
theorem facetPole_at_p_lt {y : ℝ³} (hy : y ∈ pentagonalHexecontahedron) {j k : Nat} (hj : j < 60)
    (hk : k < 60) (hjk : j < k) (hind : AffineIndependent ℝ ![snubV 0, snubV j, snubV k])
    (h0 : ⟪snubV 0, y⟫ = 1) (hjy : ⟪snubV j, y⟫ = 1) (hky : ⟪snubV k, y⟫ = 1) :
    ∃ h < 60, ∃ o < 3, y = (wiki h).toEuclideanLin (basePole o) := by
  have hok := pairOK_of hj hk
  have hle := hy.1
  have hmem : ∀ x < 60, ⟪snubV x, y⟫ ≤ 1 := fun x hx => hle _ ((mem_snub_iff _).mpr ⟨x, hx, rfl⟩)
  unfold pairOK pairOKc at hok
  split at hok
  · -- Degenerate: two of the three points coincide.
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
    exfalso
    have hinj := hind.injective
    rcases hok with (rfl | rfl) | hkj
    · exact absurd (hinj (a₁ := 0) (a₂ := 1) rfl) (by decide)
    · exact absurd (hinj (a₁ := 0) (a₂ := 2) rfl) (by decide)
    · omega
  · rename_i x₁ x₂ _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hx₁, hx₂⟩, hpos⟩, hneg⟩ := hok
    exfalso
    have h1 := sideZ_mem (show 0 < 60 by norm_num) hj hk hx₁
    have h2 := sideZ_mem (show 0 < 60 by norm_num) hj hk hx₂
    exact not_two_sided h0 hjy hky (hmem x₁ hx₁) (hmem x₂ hx₂)
      (pos_of_scaled hpos h1.1) (neg_of_scaled hneg h2.2)
  · rename_i o h m₀ m₁ m₂ _
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨ho, hh⟩, hf0⟩, hfj⟩, hfk⟩, hdet⟩ := hok
    refine ⟨h, hh, o, ho, ?_⟩
    have hdm := detZ_mem (show 0 < 60 by norm_num) hj hk
    have hd : det3 (snubV 0) (snubV j) (snubV k) ≠ 0 := by
      rcases hdet with hpos | hneg
      · exact (pos_of_scaled hpos hdm.1).ne'
      · exact (neg_of_scaled hneg hdm.2).ne
    exact eq_of_level hd h0 hjy hky (faceVertexOK_spec ho hh (by norm_num) hf0)
      (faceVertexOK_spec ho hh hj hfj) (faceVertexOK_spec ho hh hk hfk)
  · simp at hok

/-- `facetPole_at_p_lt` for any two other vertices. -/
theorem facetPole_at_p {y : ℝ³} (hy : y ∈ pentagonalHexecontahedron) {j k : Nat} (hj : j < 60)
    (hk : k < 60) (hind : AffineIndependent ℝ ![snubV 0, snubV j, snubV k])
    (h0 : ⟪snubV 0, y⟫ = 1) (hjy : ⟪snubV j, y⟫ = 1) (hky : ⟪snubV k, y⟫ = 1) :
    ∃ h < 60, ∃ o < 3, y = (wiki h).toEuclideanLin (basePole o) := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · exact facetPole_at_p_lt hy hj hk hjk hind h0 hjy hky
  · exact absurd (hind.injective (a₁ := 1) (a₂ := 2) rfl) (by decide)
  · have hswap : AffineIndependent ℝ ![snubV 0, snubV k, snubV j] := by
      have h := hind.comp_embedding (Equiv.swap (1 : Fin 3) 2).toEmbedding
      have e : ![snubV 0, snubV k, snubV j] =
          ![snubV 0, snubV j, snubV k] ∘ (Equiv.swap (1 : Fin 3) 2).toEmbedding := by
        funext i
        fin_cases i <;> rfl
      rw [e]
      exact h
    exact facetPole_at_p_lt hy hk hj hkj hswap h0 hky hjy

/-- The rotated base poles: 92 points (with repetitions in this description). -/
noncomputable def phPoles : Finset ℝ³ :=
  (Finset.range 60 ×ˢ Finset.range 3).image fun go => (wiki go.1).toEuclideanLin (basePole go.2)

theorem mem_phPoles (y : ℝ³) :
    y ∈ phPoles ↔ ∃ g < 60, ∃ o < 3, y = (wiki g).toEuclideanLin (basePole o) := by
  simp only [phPoles, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨g, o, ⟨hg, ho⟩, rfl⟩; exact ⟨g, hg, o, ho, rfl⟩
  · rintro ⟨g, hg, o, ho, rfl⟩; exact ⟨g, o, ⟨hg, ho⟩, rfl⟩

/-- **The polar dual of the snub dodecahedron is exactly the rotated base poles.** -/
theorem pentagonalHexecontahedron_eq : pentagonalHexecontahedron = (phPoles : Set ℝ³) := by
  ext y
  rw [Finset.mem_coe, mem_phPoles]
  constructor
  · intro hy
    obtain ⟨-, a, ha, b, hb, c, hc, hind, hay, hby, hcy⟩ := id hy
    obtain ⟨g, hg, rfl⟩ := (mem_snub_iff a).mp ha
    obtain ⟨j₀, hj₀, rfl⟩ := (mem_snub_iff b).mp hb
    obtain ⟨k₀, hk₀, rfl⟩ := (mem_snub_iff c).mp hc
    -- Move vertex g to p with W = S_g⁻¹ = S_gᵀ.
    obtain ⟨hgi, hgiT⟩ := wiki_inv hg
    set W := wiki (wikiInv g)
    have hW : ∀ x z, ⟪W.toEuclideanLin x, W.toEuclideanLin z⟫ = ⟪x, z⟫ := wiki_inner hgi
    have hWp : W.toEuclideanLin (snubV g) = snubV 0 := by
      rw [snubV, ← IModel.toEuclideanLin_mul, hgiT, wiki_transpose_mul hg, snubV_zero]
      simp
    obtain ⟨j, hj, hWj⟩ := wiki_snubV hgi hj₀
    obtain ⟨k, hk, hWk⟩ := wiki_snubV hgi hk₀
    have hy' : W.toEuclideanLin y ∈ pentagonalHexecontahedron := wiki_facetPoles hgi hy
    have hinj : Function.Injective W.toEuclideanLin := by
      intro u v huv
      have := congrArg (wiki g).toEuclideanLin huv
      rwa [← IModel.toEuclideanLin_mul, ← IModel.toEuclideanLin_mul, hgiT,
        wiki_mul_transpose hg, Matrix.toLpLin_one, LinearMap.id_apply, LinearMap.id_apply] at this
    have hind' : AffineIndependent ℝ ![snubV 0, snubV j, snubV k] := by
      have h := hind.map' (W.toEuclideanLin.toAffineMap) hinj
      have e : ![snubV 0, snubV j, snubV k] = (W.toEuclideanLin.toAffineMap) ∘
          ![snubV g, snubV j₀, snubV k₀] := by
        funext i
        fin_cases i
        · exact hWp.symm
        · exact hWj.symm
        · exact hWk.symm
      rw [e]
      exact h
    obtain ⟨h, hh, o, ho, hyo⟩ := facetPole_at_p hy' hj hk hind'
      (by rw [← hWp, hW]; exact hay) (by rw [← hWj, hW]; exact hby) (by rw [← hWk, hW]; exact hcy)
    -- y = S_g (W y) = S_g S_h (base pole).
    obtain ⟨m, hm, hmul⟩ := exists_wiki_mul g h hg hh
    refine ⟨m, hm, o, ho, ?_⟩
    have : y = (wiki g).toEuclideanLin (W.toEuclideanLin y) := by
      rw [← IModel.toEuclideanLin_mul, hgiT, wiki_mul_transpose hg]
      simp
    rw [this, hyo, ← IModel.toEuclideanLin_mul, hmul]
  · rintro ⟨g, hg, o, ho, rfl⟩
    exact wiki_facetPoles hg (basePole_mem ho)

/-! ### The base poles in the 5-fold frame: an `IModel` -/

def phScale : ℚ := (phScaleNum : ℚ) / 10 ^ 40

def orbitWikiOf (o : Nat) : Nat := orbitWiki.getD o 0

/-- The model's base point of orbit o: phScale · T · S_{g_o} (base pole o). -/
noncomputable def phV0 (o : Fin orbitCount) : ℝ³ :=
  (phScale : ℝ) • snubFrame.toEuclideanLin ((wiki (orbitWikiOf o.val)).toEuclideanLin (basePole o.val))

/-- The pole's numerator b × c + c × a + a × b, enclosed. -/
def crossSumIv (a b c : Nat) (r : Fin 3) : Iv :=
  match r with
  | 0 => ((((vIv b 1).mul (vIv c 2)).sub ((vIv b 2).mul (vIv c 1))).add
      (((vIv c 1).mul (vIv a 2)).sub ((vIv c 2).mul (vIv a 1)))).add
        (((vIv a 1).mul (vIv b 2)).sub ((vIv a 2).mul (vIv b 1)))
  | 1 => ((((vIv b 2).mul (vIv c 0)).sub ((vIv b 0).mul (vIv c 2))).add
      (((vIv c 2).mul (vIv a 0)).sub ((vIv c 0).mul (vIv a 2)))).add
        (((vIv a 2).mul (vIv b 0)).sub ((vIv a 0).mul (vIv b 2)))
  | 2 => ((((vIv b 0).mul (vIv c 1)).sub ((vIv b 1).mul (vIv c 0))).add
      (((vIv c 0).mul (vIv a 1)).sub ((vIv c 1).mul (vIv a 0)))).add
        (((vIv a 0).mul (vIv b 1)).sub ((vIv a 1).mul (vIv b 0)))

/-- A box around base pole o. -/
def poleBox (o : Nat) : RatBox where
  lo r := ((detIv (fv o 0) (fv o 1) (fv o 2)).inv.mul (crossSumIv (fv o 0) (fv o 1) (fv o 2) r)).lo
  hi r := ((detIv (fv o 0) (fv o 1) (fv o 2)).inv.mul (crossSumIv (fv o 0) (fv o 1) (fv o 2) r)).hi

theorem basePole_mem_box {o : Nat} (ho : o < 3) : (poleBox o).Mem (basePole o) := by
  have h0 := fv_lt ho (show 0 < 3 by norm_num)
  have h1 := fv_lt ho (show 1 < 3 by norm_num)
  have h2 := fv_lt ho (show 2 < 3 by norm_num)
  have hdinv := Iv.inv_mem (baseCheck_spec ho).2.2.2.1 (detIv_mem h0 h1 h2)
  have va := vIv_mem h0
  have vb := vIv_mem h1
  have vc := vIv_mem h2
  intro r
  have key := Iv.mul_mem hdinv (show (crossSumIv (fv o 0) (fv o 1) (fv o 2) r).Mem
      ((WithLp.toLp 2 ![
        (snubV (fv o 1) 1 * snubV (fv o 2) 2 - snubV (fv o 1) 2 * snubV (fv o 2) 1) +
          (snubV (fv o 2) 1 * snubV (fv o 0) 2 - snubV (fv o 2) 2 * snubV (fv o 0) 1) +
          (snubV (fv o 0) 1 * snubV (fv o 1) 2 - snubV (fv o 0) 2 * snubV (fv o 1) 1),
        (snubV (fv o 1) 2 * snubV (fv o 2) 0 - snubV (fv o 1) 0 * snubV (fv o 2) 2) +
          (snubV (fv o 2) 2 * snubV (fv o 0) 0 - snubV (fv o 2) 0 * snubV (fv o 0) 2) +
          (snubV (fv o 0) 2 * snubV (fv o 1) 0 - snubV (fv o 0) 0 * snubV (fv o 1) 2),
        (snubV (fv o 1) 0 * snubV (fv o 2) 1 - snubV (fv o 1) 1 * snubV (fv o 2) 0) +
          (snubV (fv o 2) 0 * snubV (fv o 0) 1 - snubV (fv o 2) 1 * snubV (fv o 0) 0) +
          (snubV (fv o 0) 0 * snubV (fv o 1) 1 - snubV (fv o 0) 1 * snubV (fv o 1) 0)] : ℝ³) r)
      from by
        fin_cases r <;>
        exact Iv.add_mem (Iv.add_mem (Iv.sub_mem (Iv.mul_mem (vb _) (vc _)) (Iv.mul_mem (vb _) (vc _)))
          (Iv.sub_mem (Iv.mul_mem (vc _) (va _)) (Iv.mul_mem (vc _) (va _))))
            (Iv.sub_mem (Iv.mul_mem (va _) (vb _)) (Iv.mul_mem (va _) (vb _))))
  simp only [poleBox, basePole, pole, PiLp.smul_apply, smul_eq_mul]
  exact key

def phV0Box (o : Fin orbitCount) : RatBox :=
  let B := imageBoxK snubFrameT (imageBoxK (wikiEntry (orbitWikiOf o.val)) (poleBox o.val))
  ⟨fun r => phScale * B.lo r, fun r => phScale * B.hi r⟩

theorem phScale_pos : (0 : ℝ) < (phScale : ℝ) := by norm_num [phScale, phScaleNum]

theorem orbitWiki_lt : ∀ o < 3, orbitWikiOf o < 60 := by decide

theorem phV0_mem (o : Fin orbitCount) : (phV0Box o).Mem (phV0 o) := by
  have ho : o.val < 3 := o.isLt
  have h1 := imageK_mem (wikiEntry (orbitWikiOf o.val)) _ (basePole_mem_box ho)
  have h2 : (imageBoxK snubFrameT (imageBoxK (wikiEntry (orbitWikiOf o.val)) (poleBox o.val))).Mem
      (snubFrame.toEuclideanLin ((wiki (orbitWikiOf o.val)).toEuclideanLin (basePole o.val))) :=
    imageK_mem snubFrameT _ h1
  intro r
  obtain ⟨hl, hh⟩ := h2 r
  have hs := phScale_pos
  simp only [phV0Box, phV0, PiLp.smul_apply, smul_eq_mul]
  push_cast
  exact ⟨mul_le_mul_of_nonneg_left hl hs.le, mul_le_mul_of_nonneg_left hh hs.le⟩

theorem phClose : closeCheck phV0Box = true := by decide +kernel

/-- Decided: for each orbit o and model stabilizer element h, with
[σ, q, τ] = stabConj[o][h]: ico h T = T S_σ, S_σ S_{g_o} = S_q = S_{g_o} S_τ,
τ ∈ baseStab o. -/
def stabRow (o h : Nat) : List Nat := (stabConj.getD o []).getD h []

def stabConjCheck : Bool :=
  (List.range 3).all fun o =>
    (icoStab o).all (· < 60) &&
      (List.range 60).all fun h =>
        !((icoStab o).contains h) ||
          match stabRow o h with
          | [σ, q, τ] =>
              decide (M3.mul8 (icoEntry h) snubFrameT = M3.mul8 snubFrameT (wikiEntry σ)) &&
              decide (M3.mul8 (wikiEntry σ) (wikiEntry (orbitWikiOf o)) = M3.scale 160 (wikiEntry q)) &&
              decide (M3.mul8 (wikiEntry (orbitWikiOf o)) (wikiEntry τ) = M3.scale 160 (wikiEntry q)) &&
              (baseStabOf o).contains τ
          | _ => false

theorem stabConjCheck_eq : stabConjCheck = true := by decide +kernel

theorem ico_mul_snubFrame_of {h σ : Nat}
    (hc : M3.mul8 (icoEntry h) snubFrameT = M3.mul8 snubFrameT (wikiEntry σ)) :
    ico h * snubFrame = snubFrame * wiki σ := by
  have h' := congrArg M3.toMatrix hc
  rw [M3.toMatrix_mul8, M3.toMatrix_mul8] at h'
  have h8 : (icoEntry h).toMatrix * snubFrameT.toMatrix =
      snubFrameT.toMatrix * (wikiEntry σ).toMatrix := by
    have := congrArg (fun M => (1 / 8 : ℝ) • M) h'
    simp only [smul_smul] at this
    norm_num at this
    exact this
  rw [ico, snubFrame, wiki, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, h8]

theorem phV0_fixed (o : Fin orbitCount) (h : Nat) (hh : h ∈ icoStab o.val) :
    (ico h).toEuclideanLin (phV0 o) = phV0 o := by
  have hc := stabConjCheck_eq
  simp only [stabConjCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
  obtain ⟨hlt, hrows⟩ := hc o.val o.isLt
  have h60 : h < 60 := by simpa using hlt h hh
  have hrow := hrows h h60
  have hcont : (icoStab o.val).contains h = true := List.contains_iff_mem.mpr hh
  rw [hcont, Bool.not_true, Bool.false_or] at hrow
  revert hrow
  split
  · rename_i σ q τ _
    intro hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hrow
    obtain ⟨⟨⟨hT, hq⟩, hq'⟩, hτ⟩ := hrow
    obtain ⟨hτ60, hfix⟩ := baseStab_fix o.isLt hτ
    rw [phV0, map_smul, ← IModel.toEuclideanLin_mul, ico_mul_snubFrame_of hT,
      IModel.toEuclideanLin_mul snubFrame (wiki σ), ← IModel.toEuclideanLin_mul (wiki σ),
      wiki_mul_of_mul8' hq, ← wiki_mul_of_mul8' hq', IModel.toEuclideanLin_mul, hfix]
  · intro hrow
    simp at hrow

/-- The pentagonal hexecontahedron, scaled and rotated into the 5-fold frame, as an
`IModel`. -/
noncomputable def phIModel : IModel :=
  IModel.ofBoxes phV0Box phClose phV0 phV0_mem phV0_fixed

/-! #### Its vertices are the poles -/

def slotSigmaOf (i : Nat) : Nat := slotSigma.getD i 0
def slotWikiOf (i : Nat) : Nat := slotWiki.getD i 0
def coverRow (o g : Nat) : List Nat := (orbitCover.getD o []).getD g []

/-- Decided: slot i is phScale · T · S_{w_i} (base pole of its orbit), and every
rotated base pole is a slot. -/
def slotCheck : Bool :=
  ((List.range (Fintype.card VertexIndex)).all fun i =>
    decide (slotWikiOf i < 60) &&
    decide (M3.mul8 (icoEntry (vElem i)) snubFrameT = M3.mul8 snubFrameT (wikiEntry (slotSigmaOf i))) &&
    decide (M3.mul8 (wikiEntry (slotSigmaOf i)) (wikiEntry (orbitWikiOf (vOrbit i).val)) =
      M3.scale 160 (wikiEntry (slotWikiOf i)))) &&
  ((List.range 3).all fun o => (List.range 60).all fun g =>
    match coverRow o g with
    | [i, τ] => decide (i < Fintype.card VertexIndex) && decide ((vOrbit i).val = o) &&
        decide (M3.mul8 (wikiEntry (slotWikiOf i)) (wikiEntry τ) = M3.scale 160 (wikiEntry g)) &&
        (baseStabOf o).contains τ
    | _ => false)

theorem slotCheck_eq : slotCheck = true := by decide +kernel

theorem phIModel_vertex (i : VertexIndex) :
    phIModel.toC5.vertex i = (phScale : ℝ) • snubFrame.toEuclideanLin
      ((wiki (slotWikiOf i.val)).toEuclideanLin (basePole (vOrbit i.val).val)) := by
  have hc := slotCheck_eq
  simp only [slotCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  obtain ⟨⟨-, hT⟩, hw⟩ := hc.1 i.val (by simpa using i.isLt)
  rw [IModel.toC5_vertex, IModel.orbit]
  change (ico (vElem i.val)).toEuclideanLin (phV0 (vOrbit i.val)) = _
  rw [phV0, map_smul, ← IModel.toEuclideanLin_mul, ico_mul_snubFrame_of hT,
    IModel.toEuclideanLin_mul snubFrame (wiki (slotSigmaOf i.val)),
    ← IModel.toEuclideanLin_mul (wiki (slotSigmaOf i.val)), wiki_mul_of_mul8' hw]

theorem phIModel_verts :
    (phIModel.toC5.verts : Set ℝ³) =
      (fun x => (phScale : ℝ) • snubFrame.toEuclideanLin x) '' (phPoles : Set ℝ³) := by
  have hc := slotCheck_eq
  simp only [slotCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  ext v
  simp only [C5Model.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
    Set.mem_image, Finset.mem_coe, mem_phPoles]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨slotWikiOf i.val, (hc.1 i.val (by simpa using i.isLt)).1.1, (vOrbit i.val).val,
      (vOrbit i.val).isLt, rfl⟩, (phIModel_vertex i).symm⟩
  · rintro ⟨_, ⟨g, hg, o, ho, rfl⟩, rfl⟩
    have hrow := hc.2 o ho g hg
    revert hrow
    split
    · rename_i i τ _
      intro hrow
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hrow
      obtain ⟨⟨⟨hi, hio⟩, hmul⟩, hτ⟩ := hrow
      refine ⟨⟨i, by simpa using hi⟩, ?_⟩
      rw [phIModel_vertex]
      simp only [hio]
      rw [← wiki_mul_of_mul8' hmul, IModel.toEuclideanLin_mul, (baseStab_fix ho hτ).2]
    · intro hrow
      simp at hrow

/-! ### Main theorem -/

/-- If no `IModel` is Rupert (what `constructPentagonalHexecontahedron` checks),
then no pentagonal hexecontahedron is Rupert. -/
theorem pentagonalHexecontahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, IsPentagonalHexecontahedron V → ¬ IsRupert V := by
  rintro V ⟨c, s, M, hs, hM, hV⟩ hr
  apply h phIModel
  -- phIModel's vertices are V under x ↦ phScale T s⁻¹ Mᵀ (x − c), a similarity.
  have hMt : Mᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    simpa using (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hM
  have hMM : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
  have hTM : snubFrame * Mᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ snubFrame_orthogonal hMt
  have hk : (0 : ℝ) < (phScale : ℝ) * s⁻¹ := mul_pos phScale_pos (inv_pos.mpr hs)
  have hsim := isRupert_image_similarity
    (-(((phScale : ℝ) * s⁻¹) • (snubFrame * Mᵀ).toEuclideanLin c)) _ hk _ hTM _ hr
  convert hsim using 1
  apply Finset.coe_injective
  rw [Finset.coe_image, hV, phIModel_verts, pentagonalHexecontahedron_eq, Set.image_image]
  congr 1
  funext x
  have hx : (snubFrame * Mᵀ).toEuclideanLin (M.toEuclideanLin x) = snubFrame.toEuclideanLin x := by
    rw [← IModel.toEuclideanLin_mul, Matrix.mul_assoc, hMM, Matrix.mul_one]
  simp only [Function.comp, map_add, map_smul, hx, smul_add, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
  abel

/-- The polar dual of Wikipedia's snub dodecahedron is a finite set (92 points). -/
theorem pentagonalHexecontahedron_finite :
    ∃ V : Finset ℝ³, (V : Set ℝ³) = pentagonalHexecontahedron :=
  ⟨phPoles, pentagonalHexecontahedron_eq.symm⟩

/-- **Main theorem.** The polar dual of Wikipedia's snub dodecahedron is not
Rupert, given that no `IModel` is (what `constructPentagonalHexecontahedron`
checks). -/
theorem polarDualSnubDodecahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, (V : Set ℝ³) = pentagonalHexecontahedron → ¬ IsRupert V := by
  intro V hV
  refine pentagonalHexecontahedron_not_rupert h V ⟨0, 1, 1, one_pos, Submonoid.one_mem _, ?_⟩
  have hid : (fun x : ℝ³ => (0 : ℝ³) + (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ).toEuclideanLin x) = id := by
    funext x
    simp
  rw [hV, hid, Set.image_id]

end Noperthedron.SnubDodecahedron
