module

public import Noperthedron.PentagonalHexecontahedron.IcoModel
public import Noperthedron.MainTheorem

@[expose] public section

/-!
# Instantiating `IModel` from rational enclosures of the base points

`IModel.ofBoxes`: if each orbit's base point `v0 o` lies in a rational box
`B o` and is fixed by the orbit's stabilizer, and the decided check
`closeCheck B` passes, then the base points define an `IModel`. The check
pushes the boxes through each slot's rotation g_i = `vElem i` by interval
arithmetic (entries enclosed by `IcoZ.lo`/`IcoZ.hi`) and bounds the distance
of the image box to `rationalVertex i` by `modelErrorQ`.
-/

namespace Noperthedron.PentagonalHexecontahedron

open scoped Matrix

/-- A closed rational box. -/
structure RatBox where
  lo : Fin 3 → ℚ
  hi : Fin 3 → ℚ

def RatBox.Mem (B : RatBox) (v : ℝ³) : Prop := ∀ c, (B.lo c : ℝ) ≤ v c ∧ v c ≤ (B.hi c : ℝ)

/-- Enclosure of a product of two intervals. -/
def mulLo (a b c d : ℚ) : ℚ := min (min (a * c) (a * d)) (min (b * c) (b * d))

def mulHi (a b c d : ℚ) : ℚ := max (max (a * c) (a * d)) (max (b * c) (b * d))

theorem min_mul_le {p q t k : ℝ} (hp : p ≤ t) (hq : t ≤ q) : min (p * k) (q * k) ≤ t * k := by
  rcases le_total 0 k with hk | hk
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

theorem mul_le_max {p q t k : ℝ} (hp : p ≤ t) (hq : t ≤ q) : t * k ≤ max (p * k) (q * k) := by
  rcases le_total 0 k with hk | hk
  · exact (by nlinarith : t * k ≤ q * k).trans (le_max_right _ _)
  · exact (by nlinarith : t * k ≤ p * k).trans (le_max_left _ _)

theorem mulLo_le {a b c d : ℚ} {x y : ℝ} (hx : (a : ℝ) ≤ x ∧ x ≤ b) (hy : (c : ℝ) ≤ y ∧ y ≤ d) :
    (mulLo a b c d : ℝ) ≤ x * y := by
  unfold mulLo
  push_cast
  -- x y ≥ min (x c) (x d), and x c ≥ min (a c) (b c), x d ≥ min (a d) (b d).
  have h1 : min ((c : ℝ) * x) (d * x) ≤ y * x := min_mul_le hy.1 hy.2
  have h2 : min ((a : ℝ) * c) (b * c) ≤ x * c := min_mul_le hx.1 hx.2
  have h3 : min ((a : ℝ) * d) (b * d) ≤ x * d := min_mul_le hx.1 hx.2
  have e1 : (y : ℝ) * x = x * y := by ring
  rw [e1, mul_comm (c : ℝ) x, mul_comm (d : ℝ) x] at h1
  refine le_trans ?_ h1
  apply le_min
  · exact (min_le_min (min_le_left _ _) (min_le_left _ _)).trans h2
  · exact (min_le_min (min_le_right _ _) (min_le_right _ _)).trans h3

theorem le_mulHi {a b c d : ℚ} {x y : ℝ} (hx : (a : ℝ) ≤ x ∧ x ≤ b) (hy : (c : ℝ) ≤ y ∧ y ≤ d) :
    x * y ≤ (mulHi a b c d : ℝ) := by
  unfold mulHi
  push_cast
  have h1 : y * x ≤ max ((c : ℝ) * x) (d * x) := mul_le_max hy.1 hy.2
  have h2 : x * c ≤ max ((a : ℝ) * c) (b * c) := mul_le_max hx.1 hx.2
  have h3 : x * d ≤ max ((a : ℝ) * d) (b * d) := mul_le_max hx.1 hx.2
  have e1 : (y : ℝ) * x = x * y := by ring
  rw [e1, mul_comm (c : ℝ) x, mul_comm (d : ℝ) x] at h1
  refine h1.trans ?_
  apply max_le
  · exact h2.trans (max_le_max (le_max_left _ _) (le_max_left _ _))
  · exact h3.trans (max_le_max (le_max_right _ _) (le_max_right _ _))

/-- Enclosure of `(ico g *ᵥ v) r` for v in B. -/
def imageLo (g : Nat) (B : RatBox) (r : Fin 3) : ℚ :=
  ∑ c, mulLo (IcoZ.lo ((icoEntry g).entry r c) / 20) (IcoZ.hi ((icoEntry g).entry r c) / 20)
    (B.lo c) (B.hi c)

def imageHi (g : Nat) (B : RatBox) (r : Fin 3) : ℚ :=
  ∑ c, mulHi (IcoZ.lo ((icoEntry g).entry r c) / 20) (IcoZ.hi ((icoEntry g).entry r c) / 20)
    (B.lo c) (B.hi c)

/-- A bound on `(x − q)²` for x in [lo, hi]. -/
def sqDistBound (lo hi q : ℚ) : ℚ := max ((lo - q) ^ 2) ((hi - q) ^ 2)

def closeCheck (B : Fin orbitCount → RatBox) : Bool :=
  (List.finRange (Fintype.card VertexIndex)).all fun n =>
    let i : VertexIndex := Fin.cast (by simp) n
    let b := B (vOrbit i.val)
    decide (∑ r, sqDistBound (imageLo (vElem i.val) b r) (imageHi (vElem i.val) b r)
      (rationalVertex i r) ≤ modelErrorQ ^ 2)

theorem image_mem (g : Nat) (B : RatBox) {v : ℝ³} (hv : B.Mem v) (r : Fin 3) :
    (imageLo g B r : ℝ) ≤ ((ico g).toEuclideanLin v) r ∧
      ((ico g).toEuclideanLin v) r ≤ (imageHi g B r : ℝ) := by
  have hentry : ∀ c, (IcoZ.lo ((icoEntry g).entry r c) / 20 : ℚ) ≤ (ico g r c : ℝ) ∧
      (ico g r c : ℝ) ≤ ((IcoZ.hi ((icoEntry g).entry r c) / 20 : ℚ) : ℝ) := by
    intro c
    have h1 := IcoZ.lo_le_val ((icoEntry g).entry r c)
    have h2 := IcoZ.val_le_hi ((icoEntry g).entry r c)
    have hval : ico g r c = IcoZ.val ((icoEntry g).entry r c) / 20 := by
      simp [ico, M3.toMatrix]
      ring
    rw [hval]
    push_cast
    constructor <;> linarith
  have happly : ((ico g).toEuclideanLin v) r = ∑ c, ico g r c * v c := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [happly]
  constructor
  · simp only [imageLo]
    push_cast
    exact Finset.sum_le_sum fun c _ => mulLo_le (hentry c) (hv c)
  · simp only [imageHi]
    push_cast
    exact Finset.sum_le_sum fun c _ => le_mulHi (hentry c) (hv c)

theorem sq_le_sqDistBound {lo hi q : ℚ} {x : ℝ} (hx : (lo : ℝ) ≤ x ∧ x ≤ hi) :
    (x - q) ^ 2 ≤ (sqDistBound lo hi q : ℝ) := by
  unfold sqDistBound
  push_cast
  obtain ⟨hl, hh⟩ := hx
  rcases le_total (q : ℝ) x with hq | hq
  · exact (by nlinarith : (x - q) ^ 2 ≤ ((hi : ℝ) - q) ^ 2).trans (le_max_right _ _)
  · exact (by nlinarith : (x - q) ^ 2 ≤ ((lo : ℝ) - q) ^ 2).trans (le_max_left _ _)

/-- Base points in checked boxes, fixed by their stabilizers, are an `IModel`. -/
noncomputable def IModel.ofBoxes (B : Fin orbitCount → RatBox) (hcheck : closeCheck B = true)
    (v0 : Fin orbitCount → ℝ³) (hv : ∀ o, (B o).Mem (v0 o))
    (hfixed : ∀ o : Fin orbitCount, ∀ h ∈ icoStab o.val, (ico h).toEuclideanLin (v0 o) = v0 o) :
    IModel where
  v0 := v0
  fixed := hfixed
  close i := by
    simp only [closeCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
      decide_eq_true_eq] at hcheck
    have hi := hcheck (Fin.cast (by simp) i)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at hi
    set b := B (vOrbit i.val)
    set w := (ico (vElem i.val)).toEuclideanLin (v0 (vOrbit i.val))
    have hsq : ‖w - toR3 (rationalVertex i)‖ ^ 2 ≤ ((modelErrorQ : ℚ) : ℝ) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      have hb : ∀ r, (w r - rationalVertex i r) ^ 2 ≤
          (sqDistBound (imageLo (vElem i.val) b r) (imageHi (vElem i.val) b r)
            (rationalVertex i r) : ℝ) :=
        fun r => sq_le_sqDistBound (image_mem _ b (hv _) r)
      have hiR : ((∑ r, sqDistBound (imageLo (vElem i.val) b r) (imageHi (vElem i.val) b r)
          (rationalVertex i r) : ℚ) : ℝ) ≤ ((modelErrorQ ^ 2 : ℚ) : ℝ) := by exact_mod_cast hi
      push_cast at hiR
      calc ∑ r, ‖(w - toR3 (rationalVertex i)) r‖ ^ 2
          = ∑ r, (w r - rationalVertex i r) ^ 2 := by
            simp [toR3, Real.norm_eq_abs, sq_abs]
        _ ≤ _ := Finset.sum_le_sum fun r _ => hb r
        _ ≤ _ := hiR
    have hpos : (0 : ℝ) ≤ (modelErrorQ : ℝ) := by norm_num [modelErrorQ]
    exact (sq_le_sq₀ (norm_nonneg _) hpos).mp hsq

/-! ### Similarities preserve Rupert-ness -/

theorem _root_.proj_xy_smul (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : proj_xy (t • v) = t • proj_xy v := by
  ext i; fin_cases i <;> simp [proj_xy]

theorem _root_.proj_xy_add (u v : EuclideanSpace ℝ (Fin 3)) : proj_xy (u + v) = proj_xy u + proj_xy v := by
  ext i; fin_cases i <;> simp [proj_xy]

/-- Rupert-ness is invariant under a nonzero scaling (a negative one is a
point reflection). -/
theorem _root_.isRupert_image_smul (t : ℝ) (ht : t ≠ 0)
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image fun x => t • x) := by
  obtain ⟨R1, hR1, off, R2, hR2, hsub⟩ := h
  refine ⟨R1, hR1, t • off, R2, hR2, ?_⟩
  dsimp only at hsub ⊢
  have hhull : convexHull ℝ (↑(V.image fun x => t • x) : Set (EuclideanSpace ℝ (Fin 3))) =
      (fun x => t • x) '' convexHull ℝ ↑V := by
    rw [Finset.coe_image]
    have := LinearMap.image_convexHull (t • (LinearMap.id : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _))
      (↑V : Set (EuclideanSpace ℝ (Fin 3)))
    simpa using this.symm
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) := Homeomorph.smulOfNeZero t ht
  have himg : ∀ (o : EuclideanSpace ℝ (Fin 2)) (R : Matrix (Fin 3) (Fin 3) ℝ),
      { x | ∃ p ∈ convexHull ℝ (↑(V.image fun x => t • x) : Set (EuclideanSpace ℝ (Fin 3))),
          t • o + proj_xy (R.toEuclideanLin p) = x } =
        e '' { x | ∃ p ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin 3))),
          o + proj_xy (R.toEuclideanLin p) = x } := by
    intro o R
    rw [hhull]
    ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨o + proj_xy (R.toEuclideanLin q), ⟨q, hq, rfl⟩, ?_⟩
      simp [e, Homeomorph.smulOfNeZero, map_smul, proj_xy_smul, smul_add]
    · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨t • q, ⟨q, hq, rfl⟩, ?_⟩
      simp [e, Homeomorph.smulOfNeZero, map_smul, proj_xy_smul, smul_add]
  have h1 := himg off R1
  have h2 := himg 0 R2
  simp only [smul_zero, zero_add] at h2
  rw [h1, h2, ← e.image_interior]
  exact Set.image_mono hsub

/-- Rupert-ness is invariant under translation. -/
theorem _root_.isRupert_image_add (c : EuclideanSpace ℝ (Fin 3))
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image fun x => c + x) := by
  obtain ⟨R1, hR1, off, R2, hR2, hsub⟩ := h
  let d := proj_xy (R2.toEuclideanLin c)
  refine ⟨R1, hR1, off + d - proj_xy (R1.toEuclideanLin c), R2, hR2, ?_⟩
  dsimp only at hsub ⊢
  have hhull : convexHull ℝ (↑(V.image fun x => c + x) : Set (EuclideanSpace ℝ (Fin 3))) =
      (fun x => c + x) '' convexHull ℝ ↑V := by
    rw [Finset.coe_image]
    have := AffineMap.image_convexHull
      (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 3)) c).toAffineMap
      (↑V : Set (EuclideanSpace ℝ (Fin 3)))
    simpa [vadd_eq_add] using this.symm
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) := Homeomorph.addRight d
  have himg : ∀ (o o' : EuclideanSpace ℝ (Fin 2)) (R : Matrix (Fin 3) (Fin 3) ℝ),
      o' = o + d - proj_xy (R.toEuclideanLin c) →
      { x | ∃ p ∈ convexHull ℝ (↑(V.image fun x => c + x) : Set (EuclideanSpace ℝ (Fin 3))),
          o' + proj_xy (R.toEuclideanLin p) = x } =
        e '' { x | ∃ p ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin 3))),
          o + proj_xy (R.toEuclideanLin p) = x } := by
    intro o o' R ho
    rw [hhull]
    ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨o + proj_xy (R.toEuclideanLin q), ⟨q, hq, rfl⟩, ?_⟩
      simp only [e, Homeomorph.coe_addRight, ho, map_add, proj_xy_add]
      abel
    · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨c + q, ⟨q, hq, rfl⟩, ?_⟩
      simp only [e, Homeomorph.coe_addRight, ho, map_add, proj_xy_add]
      abel
  have h1 := himg off _ R1 rfl
  have h2 := himg 0 0 R2 (by simp [d])
  simp only [zero_add] at h2
  rw [h1, h2, ← e.image_interior]
  exact Set.image_mono hsub
/-- Rupert-ness is invariant under rotating the vertex set. -/
theorem _root_.isRupert_image_rotation (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image Q.toEuclideanLin) := by
  obtain ⟨R1, hR1, off, R2, hR2, hsub⟩ := h
  have hQt : Qᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have := (Matrix.mem_specialOrthogonalGroup_iff).mp hQ
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    exact ⟨by simpa using (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp this.1,
      by simpa using this.2⟩
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hQ.1
  have hhull : convexHull ℝ (↑(V.image Q.toEuclideanLin) : Set (EuclideanSpace ℝ (Fin 3))) =
      Q.toEuclideanLin '' convexHull ℝ ↑V := by
    rw [Finset.coe_image, LinearMap.image_convexHull]
  have hback : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (p : EuclideanSpace ℝ (Fin 3)),
      (R * Qᵀ).toEuclideanLin (Q.toEuclideanLin p) = R.toEuclideanLin p := by
    intro R p
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hQtQ]
  have hset : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (o : EuclideanSpace ℝ (Fin 2)),
      { x | ∃ p ∈ convexHull ℝ (↑(V.image Q.toEuclideanLin) : Set (EuclideanSpace ℝ (Fin 3))),
          o + proj_xy ((R * Qᵀ).toEuclideanLin p) = x } =
        { x | ∃ p ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin 3))),
          o + proj_xy (R.toEuclideanLin p) = x } := by
    intro R o
    rw [hhull]
    ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, by rw [hback]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨Q.toEuclideanLin q, ⟨q, hq, rfl⟩, by rw [hback]⟩
  refine ⟨R1 * Qᵀ, Submonoid.mul_mem _ hR1 hQt, off, R2 * Qᵀ,
    Submonoid.mul_mem _ hR2 hQt, ?_⟩
  dsimp only at hsub ⊢
  have h2 := hset R2 0
  simp only [zero_add] at h2
  rw [hset R1 off, h2]
  exact hsub


/-- Rupert-ness is invariant under every similarity x ↦ c + s M x (s > 0, M
orthogonal, including reflections). -/
theorem _root_.isRupert_image_similarity (c : EuclideanSpace ℝ (Fin 3)) (s : ℝ) (hs : 0 < s)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image fun x => c + s • M.toEuclideanLin x) := by
  have hdet : M.det = 1 ∨ M.det = -1 := by
    have hMM : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
    have := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rcases mul_self_eq_one_iff.mp this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  -- M = σ Q with Q a rotation and σ = ±1; then x ↦ c + (σ s) Q x.
  obtain ⟨Q, hQ, σ, hσ, hMQ⟩ : ∃ Q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ σ : ℝ,
      σ ≠ 0 ∧ ∀ x, M.toEuclideanLin x = σ • Q.toEuclideanLin x := by
    rcases hdet with h1 | h1
    · exact ⟨M, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hM, h1⟩, 1, one_ne_zero,
        fun x => by simp⟩
    · refine ⟨-M, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩, -1, by norm_num,
        fun x => by simp [Matrix.toLpLin_apply]⟩
      · rw [Matrix.mem_orthogonalGroup_iff']
        simpa using (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
      · rw [Matrix.det_neg]
        simp [h1]; norm_num
  have h1 := isRupert_image_rotation Q hQ V h
  have h2 := isRupert_image_smul (σ * s) (mul_ne_zero hσ hs.ne') _ h1
  have h3 := isRupert_image_add c _ h2
  convert h3 using 1
  simp only [Finset.image_image]
  congr 1
  funext x
  simp [hMQ, smul_smul, mul_comm]

end Noperthedron.PentagonalHexecontahedron
