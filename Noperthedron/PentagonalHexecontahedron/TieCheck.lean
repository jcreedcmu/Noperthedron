module

public import Noperthedron.PentagonalHexecontahedron.CapCert
public import Noperthedron.PentagonalHexecontahedron.CapRow

@[expose] public section

/-!
# Tie tube certificates (the deltoidal hexecontahedron)

For a pinning normal x (the plane x⊥ holds an antipodal pair of 5-fold and of
2-fold vertices) let L = σ_x K (L_i = σ_x v_i). A pose with view u and
relative rotation R = H_u S H_x (H the half-turns) is a passage iff S L's
shadow along u lies strictly inside K's. Near S = I the shadows touch at
exact contacts, so these "ties" need the exact solid.

`TieClaim S x T ρ`: no pose whose view is in the cone over the view triangle T
and whose rotation S = H_u R H_x has trace ≥ τ(ρ) = (3 − ρ²)/(1 + ρ²) (so
S = cayley(w), |w| ≤ ρ) is Rupert. A certificate (nopert229 `tietube.cc`)
covers each face of the cube |w|∞ ≤ ρ, w = t σ (σ_f = ±1, σ = (s₁, s₂) on the
other axes, t ∈ [0, ρ]), by a binary tree in (s₁, s₂) whose leaves are
witnesses (L-vertex q, direction ±c): with d = P × c at each corner P of T,
every vertex v_j has (N(w) q − D(w) v_j)·d ≥ 0 (the cap's witness polynomial,
divided by its power of t), and |u × c| > 0 on T. These are linear in the view,
so they hold for every u in the cone, and then (R(κ v_i))·d = κ (S q)·d ≥ κ v_j·d
for all j: not Rupert (`tie_claim`).
-/

namespace Noperthedron.PentagonalHexecontahedron.Tie

open NPoly PVec Cap
open scoped Matrix RealInnerProductSpace

abbrev Triangle := Fin 3 → Fin 3 → ℚ

/-- A rational point over K. -/
def qK (P : Fin 3 → ℚ) : KVec := fun i => IcoQ.ofRat (P i)

theorem kv_qK (P : Fin 3 → ℚ) : kv (qK P) = fun i => (P i : ℝ) := by
  funext i; simp [kv, PVec.kval, qK, IcoQ.val, IcoQ.ofRat]

/-- The view Σ λ_c P_c. -/
def viewOf (T : Triangle) (lam : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => ∑ c, lam c * (T c i : ℝ)

/-! ### Cube faces: w = t σ -/

def faceA1 (f : Fin 3) : Fin 3 := if f = 0 then 1 else 0
def faceA2 (f : Fin 3) : Fin 3 := if f = 2 then 1 else 2

/-- w on face (f, sg) over the variables y = (s₁, s₂, t, ·, ·). -/
def faceW (f : Fin 3) (sg : Bool) : PVec := fun k =>
  if k = f then NPoly.scale 5 (if sg then 1 else -1) (NPoly.var 5 2)
  else if k = faceA1 f then NPoly.mul 5 (NPoly.var 5 0) (NPoly.var 5 2)
  else NPoly.mul 5 (NPoly.var 5 1) (NPoly.var 5 2)

noncomputable def rFaceW (f : Fin 3) (sg : Bool) (y : Fin 5 → ℝ) : Fin 3 → ℝ := fun k =>
  if k = f then ((if sg then 1 else -1 : ℚ) : ℝ) * y 2
  else if k = faceA1 f then y 0 * y 2 else y 1 * y 2

theorem eval_faceW (f : Fin 3) (sg : Bool) (y : Fin 5 → ℝ) : (faceW f sg).eval y = rFaceW f sg y := by
  funext k
  simp only [PVec.eval, faceW, rFaceW]
  split_ifs <;> simp [NPoly.eval_scale, NPoly.eval_mul, NPoly.eval_var]

/-- The face's root box: s₁, s₂ ∈ [−1, 1], t ∈ [0, ρ] (boxes are (lo, width)). -/
def faceRoot (ρ : ℚ) : Box := ![(-1, 2), (-1, 2), (0, ρ), (0, 0), (0, 0)]

/-- The six faces, in tietube's order. -/
def faces : List (Fin 3 × Bool) := [(0, true), (0, false), (1, true), (1, false), (2, true), (2, false)]

/-- Every w with |w|∞ ≤ ρ is t σ on some face, with (s₁, s₂, t) in the face's root box. -/
theorem cube_face (ρ : ℚ) (w : Fin 3 → ℝ) (hw : ∀ k, |w k| ≤ ρ) :
    ∃ fs ∈ faces, ∃ y, InBox (faceRoot ρ) y ∧ rFaceW fs.1 fs.2 y = w := by
  -- The face of the largest coordinate.
  obtain ⟨f, hf⟩ : ∃ f : Fin 3, ∀ k, |w k| ≤ |w f| := by
    rcases le_total |w 0| |w 1| with h01 | h01 <;> rcases le_total |w 1| |w 2| with h12 | h12 <;>
      rcases le_total |w 0| |w 2| with h02 | h02
    all_goals first
      | (refine ⟨0, fun k => ?_⟩; fin_cases k <;> simp <;> linarith)
      | (refine ⟨1, fun k => ?_⟩; fin_cases k <;> simp <;> linarith)
      | (refine ⟨2, fun k => ?_⟩; fin_cases k <;> simp <;> linarith)
  set t := |w f|
  set sg : Bool := decide (0 ≤ w f)
  have hsg : w f = ((if sg then 1 else -1 : ℚ) : ℝ) * t := by
    by_cases h : 0 ≤ w f
    · simp [sg, h, t, abs_of_nonneg h]
    · push Not at h; simp [sg, not_le.mpr h, t, abs_of_neg h]
  have hσ : ∀ k, ∃ s : ℝ, -1 ≤ s ∧ s ≤ 1 ∧ w k = s * t := by
    intro k
    by_cases ht : t = 0
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      have := hf k; rw [ht] at this
      simp only [zero_mul]; exact abs_nonpos_iff.mp this
    · have htpos : 0 < t := lt_of_le_of_ne (abs_nonneg _) (Ne.symm ht)
      refine ⟨w k / t, ?_, ?_, by field_simp⟩
      · rw [le_div_iff₀ htpos]; have := hf k; rw [abs_le] at this; linarith
      · rw [div_le_iff₀ htpos]; have := hf k; rw [abs_le] at this; linarith
  obtain ⟨s1, hs1a, hs1b, hs1⟩ := hσ (faceA1 f)
  obtain ⟨s2, hs2a, hs2b, hs2⟩ := hσ (faceA2 f)
  refine ⟨(f, sg), ?_, ![s1, s2, t, 0, 0], ?_, ?_⟩
  · fin_cases f <;> cases sg <;> simp [faces]
  · intro i
    have htρ : t ≤ ρ := hw f
    fin_cases i <;> simp [faceRoot] <;> constructor <;> linarith [abs_nonneg (w f)]
  · funext k
    simp only [rFaceW]
    fin_cases f <;> fin_cases k <;>
      simp_all [faceA1, faceA2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
      linarith

/-! ### Tie data and the leaf test -/

/-- A tie node (DHTieData): pinning normal, view triangle, certified radius, children (split nodes;
empty for a certified leaf). -/
structure TieNode where
  normal : ℕ
  tri : Triangle
  rho : ℚ
  kids : List ℕ

/-- One pinning normal: x, L_i = σ_x v_i, and the witness candidates (L index, direction). -/
structure TieNormal where
  x : KVec
  L : Array KVec
  wits : Array (ℕ × KVec)

/-- Witness leaf w: candidate w / 2 with direction +c (w even) or −c (w odd). -/
def witDir (N : TieNormal) (w : ℕ) : Option (ℕ × KVec) :=
  match N.wits[w / 2]? with
  | some (i, c) => some (i, if w % 2 = 0 then c else kneg c)
  | none => none

/-- The witness polynomials at corner P (each divided by its power of t). -/
def tiePolys (V : Array KVec) (P : Fin 3 → ℚ) (f : Fin 3) (sg : Bool) (q c : KVec) : Array (NPoly 5) :=
  let parts := witnessParts (PVec.const (qK P)) (faceW f sg) q c
  V.map fun vj => NPoly.divOut 5 2 64 (witnessPoly parts vj)

/-- |u × c|² > 0 on the cone over T: every corner pair has (P_a × c)·(P_b × c) > 0. -/
def dOkT (T : Triangle) (c : KVec) : Bool :=
  (List.finRange 3).all fun a => (List.finRange 3).all fun b =>
    decide (0 < IcoQ.lo (kdot (kcross (qK (T a)) c) (kcross (qK (T b)) c)))

/-- Per used witness: the direction check and the polynomials at the three corners. -/
structure TieWit where
  q : KVec
  c : KVec
  dok : Bool
  Q : Fin 3 → Array (NPoly 5)

def tieWit (N : TieNormal) (V : Array KVec) (T : Triangle) (f : Fin 3) (sg : Bool) (w : ℕ) : Option TieWit :=
  match witDir N w with
  | some (i, c) =>
    match N.L[i]? with
    | some q => some ⟨q, c, dOkT T c, fun a => tiePolys V (T a) f sg q c⟩
    | none => none
  | none => none

/-- Bernstein degrees: at least 2 in (s₁, s₂, t), as tietube's dense tensors. -/
def tieDegs (q : NPoly 5) : Fin 5 → ℕ := fun i => if i.val < 3 then max (degs q i) 2 else degs q i

def tieBoxOk (Q : Array (NPoly 5)) (box : Box) : Bool :=
  Q.all fun q => decide (0 ≤ NPoly.lowerDeg 5 (tieDegs q) q box)

theorem tieBoxOk_sound {Q : Array (NPoly 5)} {box : Box} (hb : ∀ i, 0 ≤ (box i).2) (h : tieBoxOk Q box = true)
    {y : Fin 5 → ℝ} (hy : InBox box y) : ∀ q ∈ Q, 0 ≤ NPoly.eval 5 q y := by
  intro q hq
  have := Array.all_eq_true.mp h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hq
  have hlow := of_decide_eq_true (this i hi)
  have := lowerDeg_le_eval 5 (tieDegs Q[i]) Q[i] box y hb hy
  exact le_trans (by exact_mod_cast hlow) this

def tieLeafCheck (cache : Array (Option TieWit)) (w : ℕ) (box : Box) : Bool :=
  match cache[w]? with
  | some (some d) => d.dok && (List.finRange 3).all fun a => tieBoxOk (d.Q a) box
  | _ => false

theorem tiePolys_sound (V : Array KVec) (P : Fin 3 → ℚ) (f : Fin 3) (sg : Bool) (q c : KVec)
    (y : Fin 5 → ℝ) (ht : 0 ≤ y 2) (hQ : ∀ p ∈ tiePolys V P f sg q c, 0 ≤ NPoly.eval 5 p y) :
    ∀ vj ∈ V, 0 ≤ witnessValue (fun i => (P i : ℝ)) (rFaceW f sg y) (kv q) (kv c) (kv vj) := by
  intro vj hvj
  have hmem : NPoly.divOut 5 2 64 (witnessPoly (witnessParts (PVec.const (qK P)) (faceW f sg) q c) vj) ∈
      tiePolys V P f sg q c := Array.mem_map.mpr ⟨vj, hvj, rfl⟩
  have h0 := hQ _ hmem
  obtain ⟨m, hm⟩ := eval_divOut 5 2 y 64 (witnessPoly (witnessParts (PVec.const (qK P)) (faceW f sg) q c) vj)
  have hv := mul_nonneg (pow_nonneg ht m) h0
  rw [← hm, eval_witnessPoly, PVec.eval_const, eval_faceW] at hv
  have hP : kval (qK P) = fun i => (P i : ℝ) := kv_qK P
  rw [hP] at hv
  simpa [witnessValue, kv] using hv

theorem dOkT_sound (T : Triangle) (c : KVec) (h : dOkT T c = true) (a b : Fin 3) :
    0 < rdot (rcross (fun i => (T a i : ℝ)) (kv c)) (rcross (fun i => (T b i : ℝ)) (kv c)) := by
  simp only [dOkT, List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] at h
  have := lo_val_lt (h a b)
  rwa [val_kdot, kval_kcross, kval_kcross, kv_qK, kv_qK] at this

/-- A leaf: some witness (q, c) whose values are ≥ 0 at every corner and vertex, with |u × c| > 0. -/
def LeafGood (N : TieNormal) (V : Array KVec) (T : Triangle) (f : Fin 3) (sg : Bool) (y : Fin 5 → ℝ) : Prop :=
  0 ≤ y 2 → ∃ i c q, N.L[i]? = some q ∧ (∃ w, witDir N w = some (i, c)) ∧
    dOkT T c = true ∧
    ∀ a, ∀ vj ∈ V, 0 ≤ witnessValue (fun k => (T a k : ℝ)) (rFaceW f sg y) (kv q) (kv c) (kv vj)

/-- The face check with a witness cache for the tree's leaves. -/
def faceCheck (N : TieNormal) (V : Array KVec) (T : Triangle) (ρ : ℚ) (f : Fin 3) (sg : Bool) (t : CTree) : Bool :=
  let used := t.leafIds
  let cache : Array (Option TieWit) :=
    (Array.range (2 * N.wits.size)).map fun w => if used.contains w then tieWit N V T f sg w else none
  decide (0 ≤ ρ) && t.check (tieLeafCheck cache) (fun _ => false) (fun _ => false) (faceRoot ρ)

theorem faceRoot_width (ρ : ℚ) (hρ : 0 ≤ ρ) : ∀ i, 0 ≤ (faceRoot ρ i).2 := by
  intro i; fin_cases i <;> simp [faceRoot, hρ]

theorem faceCheck_sound (N : TieNormal) (V : Array KVec) (T : Triangle) (ρ : ℚ) (f : Fin 3) (sg : Bool)
    (t : CTree) (h : faceCheck N V T ρ f sg t = true) (y : Fin 5 → ℝ) (hy : InBox (faceRoot ρ) y) :
    LeafGood N V T f sg y := by
  simp only [faceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hρ, h⟩ := h
  set cache : Array (Option TieWit) :=
    (Array.range (2 * N.wits.size)).map fun w => if t.leafIds.contains w then tieWit N V T f sg w else none
  apply CTree.check_sound (tieLeafCheck cache) (fun _ => false) (fun _ => false) (LeafGood N V T f sg)
    ?_ (by simp) (by simp) t (faceRoot ρ) (faceRoot_width ρ hρ) h y hy
  intro w box hb hleaf y hy ht
  unfold tieLeafCheck at hleaf
  split at hleaf
  · rename_i d hd
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at hleaf
    obtain ⟨hdok, hbox⟩ := hleaf
    -- The cache entry is tieWit … w.
    have hw : tieWit N V T f sg w = some d := by
      simp only [cache, Array.getElem?_map, Array.getElem?_range] at hd
      split at hd
      · simp only [Option.map_some, Option.some.injEq] at hd
        split at hd
        · exact hd
        · cases hd
      · simp at hd
    unfold tieWit at hw
    split at hw
    · rename_i i c hwd
      split at hw
      · rename_i q hq
        simp only [Option.some.injEq] at hw
        subst hw
        refine ⟨i, c, q, hq, ⟨w, hwd⟩, hdok, ?_⟩
        intro a
        exact tiePolys_sound V (T a) f sg q c y ht (tieBoxOk_sound hb (hbox a) hy)
      · cases hw
    · cases hw
  · simp at hleaf

/-! ### The tie certificate -/

/-- The exact facts: L_i = σ_x v_i, i.e. (x·x) L_i = (x·x) v_i − 2 (v_i·x) x, and x ≠ 0. -/
def lCheck (N : TieNormal) (V : Array KVec) : Bool :=
  decide (N.L.size = V.size) && decide (0 < IcoQ.lo (kdot N.x N.x)) &&
  (List.range V.size).all fun i =>
    match N.L[i]?, V[i]? with
    | some l, some v => decide ((fun k => IcoQ.mul (kdot N.x N.x) (l k)) =
        fun k => IcoQ.sub (IcoQ.mul (kdot N.x N.x) (v k)) (IcoQ.mul (IcoQ.scale 2 (kdot v N.x)) (N.x k)))
    | _, _ => false

/-- A tie certificate for one view triangle: one tree per face. -/
def tieCertCheck (N : TieNormal) (V : Array KVec) (T : Triangle) (ρ : ℚ) (trees : List CTree) : Bool :=
  decide (trees.length = 6) && decide (0 ≤ ρ) && decide (ρ ^ 2 ≤ 3) &&
    (faces.zip trees).all fun e => faceCheck N V T ρ e.1.1 e.1.2 e.2

/-- No pose with view in the cone over T and H_u R H_x within ρ of I is Rupert. -/
def TieClaim (S : Set ℝ³) (x : Fin 3 → ℝ) (T : Triangle) (ρ : ℚ) : Prop :=
  ∀ (p : MatrixPose) (κ : ℝ) (lam : Fin 3 → ℝ), 0 < κ → (∀ c, 0 ≤ lam c) → p.view = κ • viewOf T lam →
    ((3 - (ρ : ℝ) ^ 2) / (1 + (ρ : ℝ) ^ 2)) ≤
      Matrix.trace (halfTurnMat p.view * p.relativeRotation * halfTurnMat x) →
    ¬ RupertPose p S

theorem tieClaim_mono {S : Set ℝ³} {x : Fin 3 → ℝ} {T : Triangle} {ρ ρ' : ℚ} (h : TieClaim S x T ρ)
    (h0 : 0 ≤ ρ') (hle : ρ' ≤ ρ) : TieClaim S x T ρ' := by
  intro p κ lam hκ hlam hv htr
  apply h p κ lam hκ hlam hv (le_trans ?_ htr)
  have h0' : (0 : ℝ) ≤ ρ' := by exact_mod_cast h0
  have hle' : (ρ' : ℝ) ≤ ρ := by exact_mod_cast hle
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hle' hle' h0' (le_trans h0' hle')]

/-! #### Half-turn algebra -/

theorem halfTurnMat_transpose (u : Fin 3 → ℝ) : (halfTurnMat u)ᵀ = halfTurnMat u := by
  ext i j
  simp only [Matrix.transpose_apply, halfTurnMat]
  rw [eq_comm]
  congr 1
  · ring
  · simp only [eq_comm]

theorem halfTurnMat_mem_SO3 (u : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 ≠ 0) :
    halfTurnMat u ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    show halfTurnMat u * (halfTurnMat u)ᵀ = 1
    rw [halfTurnMat_transpose, halfTurnMat_mul_self u hu]
  · rw [Matrix.det_fin_three]
    simp only [Fin.sum_univ_three] at hu
    simp only [halfTurnMat, Fin.sum_univ_three, Fin.isValue]
    simp
    field_simp
    ring

theorem halfTurnMat_mulVec (u v : Fin 3 → ℝ) :
    (halfTurnMat u).mulVec v = fun i => 2 * u i * rdot u v / (∑ k, u k ^ 2) - v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, halfTurnMat, Fin.sum_univ_three, rdot]
  fin_cases i <;> simp <;> ring

theorem halfTurnMat_perp (u d : Fin 3 → ℝ) (h : rdot u d = 0) : (halfTurnMat u).mulVec d = -d := by
  rw [halfTurnMat_mulVec, h]
  funext i; simp

theorem rdot_mulVec_transpose (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    rdot a (M.mulVec b) = rdot (Mᵀ.mulVec a) b := by
  simp only [rdot, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]; ring

/-- H_x v_i = −L_i. -/
theorem halfTurn_L (x l v : KVec) (hx : 0 < IcoQ.lo (kdot x x))
    (h : (fun k => IcoQ.mul (kdot x x) (l k)) =
      fun k => IcoQ.sub (IcoQ.mul (kdot x x) (v k)) (IcoQ.mul (IcoQ.scale 2 (kdot v x)) (x k))) :
    (halfTurnMat (kv x)).mulVec (kv v) = -kv l := by
  have hxx : 0 < rdot (kv x) (kv x) := by rw [← val_kdot]; exact lo_val_lt hx
  have hk : ∀ k, (kdot x x).val * (l k).val = (kdot x x).val * (v k).val - 2 * (kdot v x).val * (x k).val := by
    intro k
    have := congrArg IcoQ.val (congrFun h k)
    rw [show IcoQ.mul = (· * ·) from rfl, show IcoQ.sub = (· - ·) from rfl] at this
    simpa [IcoQ.val_mul, IcoQ.val_sub, IcoQ.val_scale, mul_assoc] using this
  rw [halfTurnMat_mulVec]
  funext k
  have hs : ∑ k, kv x k ^ 2 = rdot (kv x) (kv x) := by simp [rdot, Fin.sum_univ_three, sq]
  rw [hs, rdot_comm (kv x) (kv v)]
  have hk' := hk k
  rw [val_kdot, val_kdot] at hk'
  change 2 * (x k).val * rdot (kv v) (kv x) / rdot (kv x) (kv x) - (v k).val = -(l k).val
  field_simp
  linarith

/-- u × c for u = κ Σ λ_a P_a. -/
theorem rcross_view (T : Triangle) (κ : ℝ) (lam : Fin 3 → ℝ) (c : Fin 3 → ℝ) :
    rcross (κ • viewOf T lam) c = κ • ∑ a, lam a • rcross (fun k => (T a k : ℝ)) c := by
  funext k
  have e : ∀ i, (κ • viewOf T lam) i = κ * (lam 0 * (T 0 i : ℝ) + lam 1 * (T 1 i : ℝ) + lam 2 * (T 2 i : ℝ)) := by
    intro i; simp only [Pi.smul_apply, smul_eq_mul, viewOf, Fin.sum_univ_three]
  simp only [rcross, e, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Fin.sum_univ_three, Pi.add_apply]
  fin_cases k <;> simp <;> ring

theorem rdot_sum3 (A : Fin 3 → ℝ) (lam : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (κ : ℝ) :
    rdot A (κ • ∑ a, lam a • B a) = κ * ∑ a, lam a * rdot A (B a) := by
  simp only [rdot, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Fin.sum_univ_three, Pi.add_apply]
  ring

/-- The witness value is linear in the view. -/
theorem witnessValue_view (T : Triangle) (κ : ℝ) (lam : Fin 3 → ℝ) (w q c vj : Fin 3 → ℝ) :
    witnessValue (κ • viewOf T lam) w q c vj =
      κ * ∑ a, lam a * witnessValue (fun k => (T a k : ℝ)) w q c vj := by
  unfold witnessValue
  rw [rcross_view, rdot_sum3, rdot_sum3]
  simp only [Fin.sum_univ_three]
  ring

theorem rcross_view_sq (T : Triangle) (κ : ℝ) (lam : Fin 3 → ℝ) (c : Fin 3 → ℝ) :
    rdot (rcross (κ • viewOf T lam) c) (rcross (κ • viewOf T lam) c) =
      κ ^ 2 * ∑ a, ∑ b, lam a * lam b * rdot (rcross (fun k => (T a k : ℝ)) c) (rcross (fun k => (T b k : ℝ)) c) := by
  rw [rcross_view]
  set B := fun a => rcross (fun k => (T a k : ℝ)) c
  simp only [rdot, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Fin.sum_univ_three, Pi.add_apply]
  ring

/-- **Tie claims from certificates.** -/
theorem tie_claim (N : TieNormal) (V : Array KVec) (T : Triangle) (ρ : ℚ) (trees : List CTree)
    (hL : lCheck N V = true) (hc : tieCertCheck N V T ρ trees = true)
    (κs : ℝ) (hκs : 0 < κs) (S : Set ℝ³) (hSdef : S = convexHull ℝ {v | ∃ vj ∈ V.toList.map kv, v = κs • toEuc vj})
    (hSsym : ∀ v ∈ S, -v ∈ S) : TieClaim S (kv N.x) T ρ := by
  intro p κ lam hκ hlam hview htr
  simp only [tieCertCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hlen, hρ0⟩, hρ3⟩, hfaces⟩ := hc
  simp only [lCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hL
  obtain ⟨⟨hLsize, hxpos⟩, hLi⟩ := hL
  set u := p.view
  set R := p.relativeRotation
  set Hu := halfTurnMat u
  set Hx := halfTurnMat (kv N.x)
  have hu1 : ∑ k, u k ^ 2 = 1 := view_sq_sum p
  have hxx : 0 < rdot (kv N.x) (kv N.x) := by rw [← val_kdot]; exact lo_val_lt hxpos
  have hxne : ∑ k, kv N.x k ^ 2 ≠ 0 := by
    have : ∑ k, kv N.x k ^ 2 = rdot (kv N.x) (kv N.x) := by simp [rdot, Fin.sum_univ_three, sq]
    rw [this]; exact hxx.ne'
  -- S = H_u R H_x is a rotation within ρ of I.
  set Sm := Hu * R * Hx
  have hSO : Sm ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have h1 := halfTurnMat_mem_SO3 u (by rw [hu1]; norm_num)
    have h2 := Noperthedron.Atlas.MatrixPose.relativeRotation_mem_SO3 p
    have h3 := halfTurnMat_mem_SO3 (kv N.x) hxne
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ h1 h2) h3
  have hρ0' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ0
  have hρ3' : (ρ : ℝ) ^ 2 ≤ 3 := by exact_mod_cast hρ3
  have hτ : 0 ≤ (3 - (ρ : ℝ) ^ 2) / (1 + (ρ : ℝ) ^ 2) := div_nonneg (by linarith) (by positivity)
  obtain ⟨wx, wy, wz, -, hSw⟩ := Noperthedron.exists_cayleyMatrix_of_trace_nonneg Sm hSO (le_trans hτ htr)
  let w : Fin 3 → ℝ := ![wx, wy, wz]
  have hSm : Sm = cayleyMatrix (w 0) (w 1) (w 2) := hSw
  have hw2 : rdot w w ≤ (ρ : ℝ) ^ 2 := by
    apply rdot_cayley_bound hρ0'
    rw [← hSm]; exact htr
  have hwinf : ∀ k, |w k| ≤ ρ := by
    intro k
    have hnn : ∀ j, 0 ≤ w j * w j := fun j => mul_self_nonneg _
    have : w k * w k ≤ rdot w w := by
      simp only [rdot]; fin_cases k <;> simp <;> nlinarith [hnn 0, hnn 1, hnn 2]
    rw [abs_le]; constructor <;> nlinarith
  -- The face and its witness.
  obtain ⟨fs, hfs, y, hy, hyw⟩ := cube_face ρ w hwinf
  obtain ⟨tr, htrmem⟩ : ∃ tr, (fs, tr) ∈ faces.zip trees := by
    match trees, hlen with
    | [t0, t1, t2, t3, t4, t5], _ =>
      simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hfs
      rcases hfs with h | h | h | h | h | h <;> subst h <;> simp [faces]
  have hy2 : 0 ≤ y 2 := by have := (hy 2).1; simpa [faceRoot] using this
  have hface := faceCheck_sound N V T ρ fs.1 fs.2 tr (hfaces _ htrmem) y hy hy2
  obtain ⟨i, c, q, hq, -, hdok, hwit⟩ := hface
  rw [hyw] at hwit
  -- v_i with H_x v_i = −q.
  have hi : i < V.size := by
    have := (Array.getElem?_eq_some_iff.mp hq).1
    omega
  obtain ⟨vi, hvi⟩ : ∃ vi, V[i]? = some vi := ⟨V[i], Array.getElem?_eq_getElem hi⟩
  have hHx : Hx.mulVec (kv vi) = -kv q := by
    have := hLi i hi
    rw [hq, hvi] at this
    exact halfTurn_L N.x q vi hxpos (of_decide_eq_true this)
  -- d = u × c ≠ 0, and the witness values at u.
  set d := rcross u (kv c)
  have hlamsum : 0 < ∑ a, lam a := by
    by_contra hle
    push Not at hle
    have hz : ∀ a, lam a = 0 := by
      intro a
      have := Finset.sum_eq_zero_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) => hlam a) |>.mp
        (le_antisymm hle (Finset.sum_nonneg fun a _ => hlam a)) a (Finset.mem_univ _)
      exact this
    have : u = 0 := by
      rw [hview]; funext k; simp [viewOf, hz]
    rw [this] at hu1; simp at hu1
  have hd : d ≠ 0 := by
    intro h0
    have hdd : rdot d d = 0 := by rw [h0]; simp [rdot]
    simp only [d] at hdd
    rw [hview, rcross_view_sq] at hdd
    have hpos : 0 < ∑ a, ∑ b, lam a * lam b *
        rdot (rcross (fun k => (T a k : ℝ)) (kv c)) (rcross (fun k => (T b k : ℝ)) (kv c)) := by
      exact AtlasHalfTurnPrune.quad_pos _ (fun a b => dOkT_sound T c hdok a b) lam hlam hlamsum
    have : 0 < κ ^ 2 * ∑ a, ∑ b, lam a * lam b *
        rdot (rcross (fun k => (T a k : ℝ)) (kv c)) (rcross (fun k => (T b k : ℝ)) (kv c)) :=
      mul_pos (by positivity) hpos
    linarith
  have hwv : ∀ vj ∈ V, 0 ≤ witnessValue u w (kv q) (kv c) (kv vj) := by
    intro vj hvj
    rw [hview, witnessValue_view]
    apply mul_nonneg hκ.le
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hlam a) (hwit a vj hvj)
  -- (S q)·d ≥ v_j·d.
  have hD : 0 < 1 + rdot w w := by linarith [rdot_self_nonneg w]
  have hSq : ∀ vj ∈ V, rdot (kv vj) d ≤ rdot (Sm.mulVec (kv q)) d := by
    intro vj hvj
    have h := hwv vj hvj
    unfold witnessValue at h
    rw [← cayley_mulVec, ← hSm] at h
    have : rdot ((1 + rdot w w) • Sm.mulVec (kv q)) d = (1 + rdot w w) * rdot (Sm.mulVec (kv q)) d := by
      simp only [rdot, Pi.smul_apply, smul_eq_mul]; ring
    rw [this] at h
    nlinarith
  -- R = H_u S H_x, and (R v_i)·d = (S q)·d.
  have hR : R = Hu * Sm * Hx := by
    have h1 : Hu * Hu = 1 := halfTurnMat_mul_self u (by rw [hu1]; norm_num)
    have h2 : Hx * Hx = 1 := halfTurnMat_mul_self (kv N.x) hxne
    simp only [Sm]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hud : rdot u d = 0 := rdot_rcross_self u (kv c)
  have hRvi : rdot d (R.mulVec (kv vi)) = rdot (Sm.mulVec (kv q)) d := by
    rw [hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHx, rdot_mulVec_transpose, halfTurnMat_transpose,
      halfTurnMat_perp u d hud, Matrix.mulVec_neg]
    simp only [rdot, Pi.neg_apply]; ring
  set M := κs * rdot (Sm.mulVec (kv q)) d
  apply not_rupert_of_support p S hSsym (toEuc d) ?_ ?_ M ?_ (κs • toEuc (kv vi)) ?_ ?_
  · intro h0
    apply hd
    have := congrArg WithLp.ofLp h0
    simpa [toEuc] using this
  · have h2 : (p.outerRot.val.toEuclideanLin (toEuc d)) 2 = rdot u d := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, toEuc, rdot, u,
        MatrixPose.view]
    rw [h2, hud]
  · rw [hSdef]
    apply inner_le_of_mem_convexHull
    rintro v ⟨vj, hvj, rfl⟩
    rw [inner_smul_right, inner_toEuc]
    obtain ⟨vk, hvk, rfl⟩ := List.mem_map.mp hvj
    have := hSq vk (Array.mem_toList_iff.mp hvk)
    rw [show rdot d (kv vk) = rdot (kv vk) d by simp only [rdot]; ring]
    exact mul_le_mul_of_nonneg_left this hκs.le
  · rw [hSdef]
    apply subset_convexHull ℝ _
    exact ⟨kv vi, List.mem_map.mpr ⟨vi, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvi), rfl⟩, rfl⟩
  · simp only [map_smul, inner_smul_right, M]
    apply le_of_eq
    congr 1
    have : R.toEuclideanLin (toEuc (kv vi)) = toEuc (R.mulVec (kv vi)) := by
      simp [Matrix.toLpLin_apply, toEuc]
    rw [this, inner_toEuc, hRvi]

end Noperthedron.PentagonalHexecontahedron.Tie
