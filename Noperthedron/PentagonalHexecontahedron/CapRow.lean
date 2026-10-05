module

public import Noperthedron.PentagonalHexecontahedron.CapClaim

@[expose] public section

/-!
# Cap leaves of the 5D solution tree

A cap leaf (pack tag 16, `exact5d::CapLeafValid`) is a chart-0 box and a view
triangle inside one of the cap images: the image of a base cap (frame
x, e₁, e₂) under s·g (g ∈ I, s = ±1). `capLeafOk` checks, exactly in K, that
every corner P of the triangle has P·x' > 0 and |P·eᵢ'| ≤ μ₀ P·x' for the image
frame, and that the box lies in the Cayley ball |w|² ≤ wmax².
`capLeaf_sound`: given the base caps' claims, no pose of the box and triangle
(in the half-turn cell when the cap prunes) is Rupert.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec
open scoped Matrix

/-- `icoMatrix g` with exact entries. -/
def icoK (g : IcoIndex) (i j : Fin 3) : IcoQ :=
  let z := (icoEntry g.val).entry i j
  ⟨(z.a : ℚ) / 20, (z.b : ℚ) / 20, (z.c : ℚ) / 20, (z.d : ℚ) / 20⟩

theorem val_icoK (g : IcoIndex) (i j : Fin 3) : (icoK g i j).val = icoMatrix g i j := by
  simp only [icoK, IcoQ.val, icoMatrix, ico, M3.toMatrix, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    IcoZ.val]
  push_cast
  ring

/-- The image frame vector s g v, exactly. -/
def imgK (g : IcoIndex) (sgn : Bool) (v : KVec) : KVec := fun i =>
  let r := IcoQ.add (IcoQ.add (IcoQ.mul (icoK g i 0) (v 0)) (IcoQ.mul (icoK g i 1) (v 1))) (IcoQ.mul (icoK g i 2) (v 2))
  if sgn then r else IcoQ.neg r

theorem kv_imgK (g : IcoIndex) (sgn : Bool) (v : KVec) : kv (imgK g sgn v) = imgVec g sgn (kv v) := by
  funext i
  simp only [kv, PVec.kval, imgK, imgVec, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  rw [show IcoQ.add = (· + ·) from rfl, show IcoQ.mul = (· * ·) from rfl, show IcoQ.neg = (- ·) from rfl]
  cases sgn <;> simp [IcoQ.val_add, IcoQ.val_mul, val_icoK]

/-- A base cap: its exact frame, view half-width μ₀, |w|² bound, and (u0) the half-turn element. -/
structure CapBase where
  x : KVec
  e1 : KVec
  e2 : KVec
  mu0 : ℚ
  wmax2 : ℚ
  prune : Option IcoIndex

/-- An image s·g of a base cap. -/
structure CapImg where
  base : ℕ
  g : IcoIndex
  sgn : Bool

/-- P · v for a rational point P. -/
def dotQK (P : Fin 3 → ℚ) (v : KVec) : IcoQ :=
  IcoQ.add (IcoQ.add (IcoQ.scale (P 0) (v 0)) (IcoQ.scale (P 1) (v 1))) (IcoQ.scale (P 2) (v 2))

theorem val_dotQK (P : Fin 3 → ℚ) (v : KVec) : (dotQK P v).val = rdot (fun i => (P i : ℝ)) (kv v) := by
  simp only [dotQK, rdot, kv, PVec.kval]
  rw [show IcoQ.add = (· + ·) from rfl]
  simp [IcoQ.val_add, IcoQ.val_scale]

/-- A triangle corner lies in the image cone: P·x' > 0, |P·eᵢ'| ≤ μ₀ P·x'. -/
def cornerOk (b : CapBase) (img : CapImg) (P : Fin 3 → ℚ) : Bool :=
  decide (0 < IcoQ.lo (dotQK P (imgK img.g img.sgn b.x))) &&
  decide (0 ≤ IcoQ.lo (IcoQ.sub (IcoQ.scale b.mu0 (dotQK P (imgK img.g img.sgn b.x))) (dotQK P (imgK img.g img.sgn b.e1)))) &&
  decide (0 ≤ IcoQ.lo (IcoQ.add (IcoQ.scale b.mu0 (dotQK P (imgK img.g img.sgn b.x))) (dotQK P (imgK img.g img.sgn b.e1)))) &&
  decide (0 ≤ IcoQ.lo (IcoQ.sub (IcoQ.scale b.mu0 (dotQK P (imgK img.g img.sgn b.x))) (dotQK P (imgK img.g img.sgn b.e2)))) &&
  decide (0 ≤ IcoQ.lo (IcoQ.add (IcoQ.scale b.mu0 (dotQK P (imgK img.g img.sgn b.x))) (dotQK P (imgK img.g img.sgn b.e2))))

/-- The box lies in the Cayley ball |w|² ≤ wmax². -/
def ballOk (iv : AtlasInterval ℚ) (wmax2 : ℚ) : Bool :=
  decide (max (iv.min.x ^ 2) (iv.max.x ^ 2) + max (iv.min.y ^ 2) (iv.max.y ^ 2) +
    max (iv.min.z ^ 2) (iv.max.z ^ 2) ≤ wmax2)

def capLeafOk (bases : Array CapBase) (img : CapImg) (iv : AtlasInterval ℚ)
    (T : AtlasProjectiveView.Triangle ℚ) : Bool :=
  match bases[img.base]? with
  | some b => ballOk iv b.wmax2 && (List.finRange 3).all (fun c => cornerOk b img (T c))
  | none => false

theorem lo_val_lt {q : IcoQ} (h : 0 < IcoQ.lo q) : 0 < q.val :=
  lt_of_lt_of_le (by exact_mod_cast h) (IcoQ.lo_le_val q)

theorem lo_val_le {q : IcoQ} (h : 0 ≤ IcoQ.lo q) : 0 ≤ q.val :=
  le_trans (by exact_mod_cast h) (IcoQ.lo_le_val q)

/-- Corner semantics. -/
theorem cornerOk_sound (b : CapBase) (img : CapImg) (P : Fin 3 → ℚ) (h : cornerOk b img P = true) :
    let Pr : Fin 3 → ℝ := fun i => (P i : ℝ)
    0 < rdot Pr (imgVec img.g img.sgn (kv b.x)) ∧
      |rdot Pr (imgVec img.g img.sgn (kv b.e1))| ≤ b.mu0 * rdot Pr (imgVec img.g img.sgn (kv b.x)) ∧
      |rdot Pr (imgVec img.g img.sgn (kv b.e2))| ≤ b.mu0 * rdot Pr (imgVec img.g img.sgn (kv b.x)) := by
  simp only [cornerOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hx, h1a⟩, h1b⟩, h2a⟩, h2b⟩ := h
  simp only []
  rw [← kv_imgK, ← kv_imgK, ← kv_imgK]
  have ex := lo_val_lt hx
  rw [val_dotQK] at ex
  refine ⟨ex, ?_, ?_⟩
  · have a := lo_val_le h1a; have b' := lo_val_le h1b
    rw [show IcoQ.sub = (· - ·) from rfl] at a
    rw [show IcoQ.add = (· + ·) from rfl] at b'
    simp only [IcoQ.val_sub, IcoQ.val_add, IcoQ.val_scale, val_dotQK] at a b'
    rw [abs_le]; constructor <;> linarith
  · have a := lo_val_le h2a; have b' := lo_val_le h2b
    rw [show IcoQ.sub = (· - ·) from rfl] at a
    rw [show IcoQ.add = (· + ·) from rfl] at b'
    simp only [IcoQ.val_sub, IcoQ.val_add, IcoQ.val_scale, val_dotQK] at a b'
    rw [abs_le]; constructor <;> linarith

theorem sq_le_max_sq {lo hi x : ℝ} (h : lo ≤ x ∧ x ≤ hi) : x ^ 2 ≤ max (lo ^ 2) (hi ^ 2) := by
  rcases le_total 0 x with hx | hx
  · exact le_trans (by nlinarith [h.2]) (le_max_right _ _)
  · exact le_trans (by nlinarith [h.1]) (le_max_left _ _)

theorem ballOk_sound {iv : AtlasInterval ℚ} {wmax2 : ℚ} (h : ballOk iv wmax2 = true) {p : AtlasPose ℝ}
    (hp : p ∈ iv.toReal) : p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ wmax2 := by
  have hm := AtlasInterval.mem_toReal_iff.mp hp
  have hx := sq_le_max_sq (hm 2); have hy := sq_le_max_sq (hm 3); have hz := sq_le_max_sq (hm 4)
  simp only [AtlasPose.get_two, AtlasPose.get_three, AtlasPose.get_four] at hx hy hz
  have hb : (max (iv.min.x ^ 2) (iv.max.x ^ 2) + max (iv.min.y ^ 2) (iv.max.y ^ 2) +
      max (iv.min.z ^ 2) (iv.max.z ^ 2) : ℚ) ≤ wmax2 := of_decide_eq_true h
  have hb' : ((max (iv.min.x ^ 2) (iv.max.x ^ 2) + max (iv.min.y ^ 2) (iv.max.y ^ 2) +
      max (iv.min.z ^ 2) (iv.max.z ^ 2) : ℚ) : ℝ) ≤ wmax2 := by exact_mod_cast hb
  push_cast at hb'
  linarith

/-- Conjugates of group elements are group elements. -/
theorem exists_icoMatrix_conj (g g₀ : IcoIndex) : ∃ h : IcoIndex,
    icoMatrix g * icoMatrix g₀ * (icoMatrix g)ᵀ = icoMatrix h := by
  obtain ⟨k, hk⟩ := exists_icoMatrix_mul g g₀
  obtain ⟨hi, hmul⟩ := ico_mul_icoInv g.isLt
  have hinv : (icoMatrix g)ᵀ = icoMatrix ⟨icoInv g, hi⟩ := by
    have h1 := icoMatrix_transpose_mul g
    have h2 : icoMatrix g * icoMatrix ⟨icoInv g, hi⟩ = 1 := by simpa [icoMatrix] using hmul
    calc (icoMatrix g)ᵀ = (icoMatrix g)ᵀ * (icoMatrix g * icoMatrix ⟨icoInv g, hi⟩) := by rw [h2, Matrix.mul_one]
      _ = icoMatrix ⟨icoInv g, hi⟩ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨h, hh⟩ := exists_icoMatrix_mul k ⟨icoInv g, hi⟩
  exact ⟨h, by rw [hk, hinv, hh]⟩

/-- **Cap leaves are sound**: given the base caps' claims, no pose of the box (chart 0) whose view
lies over the triangle and whose relative rotation is in the half-turn cell is Rupert. -/
theorem capLeaf_sound (P : IModel) (bases : Array CapBase)
    (hclaims : ∀ b ∈ bases, CapClaim P.toC5.polyhedron.hull (kv b.x) (kv b.e1) (kv b.e2) b.mu0
      ((3 - b.wmax2) / (1 + b.wmax2)) (b.prune.map icoMatrix))
    (img : CapImg) (iv : AtlasInterval ℚ) (root : Fin 8) (T : AtlasProjectiveView.Triangle ℚ)
    (h : capLeafOk bases img iv T = true) (p : AtlasPose ℝ) (hp : p ∈ iv.toReal)
    (hcell : p.InHalfTurnCell 0) (hscale : 1 ≤ AtlasProjectiveView.viewScale root p)
    (htri : Noperthedron.Atlas.ProjectiveView.InTriangle (Noperthedron.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) P.toC5.polyhedron.hull := by
  unfold capLeafOk at h
  split at h
  swap; · exact absurd h (by simp)
  rename_i b hb
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨hball, hcorners⟩ := h
  have hbmem : b ∈ bases := Array.mem_of_getElem? hb
  set pose := p.matrixPoseWithOffset 0 offset
  -- The view: viewScale · Σ w_c T_c.
  obtain ⟨w, hw0, hw1, hwT⟩ := htri
  set κ := AtlasProjectiveView.viewScale root p
  have hκ : 0 < κ := by linarith
  have hview : pose.view = κ • (fun k => ∑ c, w c * (T c k : ℝ)) := by
    funext k
    have hk := congrFun hwT k
    simp only [AtlasProjectiveView.normalizedView, Noperthedron.Atlas.ProjectiveView.affinePoint,
      Noperthedron.Atlas.ProjectiveView.toReal] at hk
    simp only [pose, MatrixPose.view, AtlasPose.matrixPoseWithOffset_outerRot_val, rotRM_mat_row2, Pi.smul_apply,
      smul_eq_mul]
    have : eulerView p.θ p.φ k = AtlasEdgeCertificate.viewVector p k := by
      fin_cases k <;> simp [eulerView, AtlasEdgeCertificate.viewVector]
    rw [this, ← mul_div_cancel₀ (AtlasEdgeCertificate.viewVector p k) hκ.ne', hk]
  -- The cone conditions for the image frame, by linearity over the corners.
  have hlin : ∀ v : Fin 3 → ℝ, rdot pose.view v = κ * ∑ c, w c * rdot (fun i => (T c i : ℝ)) v := by
    intro v
    rw [hview]
    simp only [rdot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    ring
  have hc := fun c => cornerOk_sound b img (T c) (hcorners c)
  set x' := imgVec img.g img.sgn (kv b.x)
  set e1' := imgVec img.g img.sgn (kv b.e1)
  set e2' := imgVec img.g img.sgn (kv b.e2)
  have hx : 0 < rdot pose.view x' := by
    rw [hlin]
    apply mul_pos hκ
    have hsum : ∑ c, w c * rdot (fun i => (T c i : ℝ)) x' ≥
        ∑ c, w c * min (rdot (fun i => (T 0 i : ℝ)) x') (min (rdot (fun i => (T 1 i : ℝ)) x')
          (rdot (fun i => (T 2 i : ℝ)) x')) := by
      apply Finset.sum_le_sum; intro c _
      apply mul_le_mul_of_nonneg_left _ (hw0 c)
      fin_cases c
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (min_le_left _ _)
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
    rw [← Finset.sum_mul, hw1, one_mul] at hsum
    have hm : 0 < min (rdot (fun i => (T 0 i : ℝ)) x') (min (rdot (fun i => (T 1 i : ℝ)) x')
        (rdot (fun i => (T 2 i : ℝ)) x')) := lt_min (hc 0).1 (lt_min (hc 1).1 (hc 2).1)
    linarith
  have hcone : ∀ (e : Fin 3 → ℝ), (∀ c, |rdot (fun i => (T c i : ℝ)) e| ≤ b.mu0 * rdot (fun i => (T c i : ℝ)) x') →
      |rdot pose.view e| ≤ b.mu0 * rdot pose.view x' := by
    intro e he
    rw [hlin, hlin, abs_mul, abs_of_pos hκ]
    have : |∑ c, w c * rdot (fun i => (T c i : ℝ)) e| ≤ b.mu0 * ∑ c, w c * rdot (fun i => (T c i : ℝ)) x' := by
      calc |∑ c, w c * rdot (fun i => (T c i : ℝ)) e| ≤ ∑ c, |w c * rdot (fun i => (T c i : ℝ)) e| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ c, w c * |rdot (fun i => (T c i : ℝ)) e| := by
            apply Finset.sum_congr rfl; intro c _; rw [abs_mul, abs_of_nonneg (hw0 c)]
        _ ≤ ∑ c, w c * (b.mu0 * rdot (fun i => (T c i : ℝ)) x') := by
            apply Finset.sum_le_sum; intro c _; exact mul_le_mul_of_nonneg_left (he c) (hw0 c)
        _ = b.mu0 * ∑ c, w c * rdot (fun i => (T c i : ℝ)) x' := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
    nlinarith [this]
  -- The trace bound from the Cayley ball.
  have hR : pose.relativeRotation = cayleyMatrix p.x p.y p.z := by
    rw [AtlasPose.matrixPoseWithOffset_relativeRotation, CayleyAtlas.chartMatrix_zero, Matrix.one_mul]
  have hr2 := ballOk_sound hball hp
  have htr : (3 - (b.wmax2 : ℝ)) / (1 + b.wmax2) ≤ Matrix.trace pose.relativeRotation := by
    rw [hR, trace_cayleyMatrix]
    have hD : 0 < cayleyDenom p.x p.y p.z := cayleyDenom_pos _ _ _
    have hw : (0 : ℝ) ≤ b.wmax2 := le_trans (by positivity) hr2
    rw [div_le_div_iff₀ (by positivity) hD]
    simp only [cayleyDenom]
    nlinarith
  -- Apply the image claim.
  apply CapClaim.image P (hclaims b hbmem) img.g img.sgn pose hx (hcone _ fun c => (hc c).2.1)
    (hcone _ fun c => (hc c).2.2) (by push_cast at htr ⊢; exact htr)
  intro G₀ hG₀
  rcases hpr : b.prune with _ | g₀
  · rw [hpr] at hG₀; simp at hG₀
  · rw [hpr] at hG₀
    simp only [Option.map_some, Option.some.injEq] at hG₀
    obtain ⟨k, hk⟩ := exists_icoMatrix_conj img.g g₀
    rw [← hG₀, hk]
    have := hcell k
    have hv : pose.view = fun k => rotRM_mat p.θ p.φ 0 2 k := rfl
    rw [hv, hR]
    rw [show cayleyMatrix p.x p.y p.z = CayleyAtlas.chartMatrix 0 * cayleyMatrix p.x p.y p.z by
      rw [CayleyAtlas.chartMatrix_zero, Matrix.one_mul]]
    exact this

end Noperthedron.PentagonalHexecontahedron.Cap
