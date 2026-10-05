module

public import Noperthedron.PentagonalHexecontahedron.CapTheorem
public import Noperthedron.PentagonalHexecontahedron.CapTree

@[expose] public section

/-!
# Checking a cap certificate (witness leaves)

For a chart `id` with root box `B` and a witness (v_k, c):

* `dPoly`: |u × c|² as a polynomial; `dOk` (its Bernstein bound on B is
  positive) gives u × c ≠ 0 on B (`dOk_sound`).
* `screened`: the divided witness polynomials whose bound on B is negative;
  the others are ≥ 0 on B (`screened_sound`).
* `witnessLeafOk`: `dOk` and every screened polynomial ≥ 0 on the leaf box;
  `witnessLeafOk_sound` gives the witness disjunct of `ChartGood` on the leaf
  box (points of B).
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

def dPoly (st : Setup) (id : ChartId) (c : KVec) : NPoly 5 :=
  let d := PVec.cross (makeChart st id).u (PVec.const c)
  PVec.dot d d

theorem eval_dPoly (st : Setup) (id : ChartId) (c : KVec) (y : Fin 5 → ℝ) :
    NPoly.eval 5 (dPoly st id c) y = rdot (rcross (rChartU st id y) (kv c)) (rcross (rChartU st id y) (kv c)) := by
  simp only [dPoly, PVec.eval_dot, PVec.eval_cross, PVec.eval_const, eval_makeChart_u, kv]

def dOk (st : Setup) (pr : Params) (id : ChartId) (c : KVec) : Bool :=
  let q := dPoly st id c
  decide (0 < NPoly.lowerDeg 5 (degs q) q (rootBox st pr id))

theorem rootBox_width_nonneg (st : Setup) (pr : Params) (id : ChartId) (h : ∀ v, (rootLoHi st pr id v).1 ≤ (rootLoHi st pr id v).2) :
    ∀ i, 0 ≤ (rootBox st pr id i).2 := by
  intro i; simp only [rootBox]; linarith [h i]

theorem dOk_sound (st : Setup) (pr : Params) (id : ChartId) (c : KVec) (h : dOk st pr id c = true)
    (hw : ∀ i, 0 ≤ (rootBox st pr id i).2) (y : Fin 5 → ℝ) (hy : InBoxR (rootBox st pr id) y) :
    rcross (rChartU st id y) (kv c) ≠ 0 := by
  intro h0
  have hl := lowerDeg_le_eval 5 (degs (dPoly st id c)) (dPoly st id c) (rootBox st pr id) y hw hy
  have hpos : (0 : ℚ) < NPoly.lowerDeg 5 (degs (dPoly st id c)) (dPoly st id c) (rootBox st pr id) :=
    of_decide_eq_true h
  rw [eval_dPoly, h0] at hl
  simp [rdot] at hl
  linarith

/-- The divided witness polynomials not already ≥ 0 on the root box. -/
def screened (Q : Array (NPoly 5)) (box : Box) : Array (NPoly 5) :=
  Q.filter fun q => decide (NPoly.lowerDeg 5 (degs q) q box < 0)

theorem screened_sound (Q : Array (NPoly 5)) (box : Box) (hw : ∀ i, 0 ≤ (box i).2)
    (y : Fin 5 → ℝ) (hy : InBoxR box y) (hs : ∀ q ∈ screened Q box, 0 ≤ NPoly.eval 5 q y) :
    ∀ q ∈ Q, 0 ≤ NPoly.eval 5 q y := by
  intro q hq
  by_cases hneg : NPoly.lowerDeg 5 (degs q) q box < 0
  · exact hs q (Array.mem_filter.mpr ⟨hq, by simpa using hneg⟩)
  · push Not at hneg
    have := lowerDeg_le_eval 5 (degs q) q box y hw hy
    exact le_trans (by exact_mod_cast hneg) this

/-- The real value of the witness polynomial of the chart. -/
theorem eval_chart_witnessPoly (st : Setup) (id : ChartId) (vk c vj : KVec) (y : Fin 5 → ℝ) :
    NPoly.eval 5 (witnessPoly (witnessParts (makeChart st id).u (makeChart st id).w vk c) vj) y =
      witnessValue (rChartU st id y) (rChartW st id y) (kv vk) (kv c) (kv vj) := by
  rw [eval_witnessPoly, eval_makeChart_u, eval_makeChart_w]
  rfl

theorem rootLoHi_zero (st : Setup) (pr : Params) (id : ChartId) : rootLoHi st pr id 0 = (0, pr.mu0) := by
  unfold rootLoHi; simp [baseLoHi]

theorem rootLoHi_two_cone (st : Setup) (pr : Params) (id : ChartId) (hk : id.kind = .cone ∨ id.kind = .mcone)
    (hax : id.axis < 3) : rootLoHi st pr id 2 = (0, pr.t0) := by
  have hnfe : id.kind ≠ .fe := by rcases hk with h | h <;> rw [h] <;> simp
  have hnw : ¬ IsWeakP st id 0 := by
    rintro ⟨i, -, -, hi⟩; have := pvarOf_ne_zero_of_ne_fe id hnfe hi; omega
  have hb : baseLoHi st pr id.kind id.axis 2 = (0, pr.t0) := by
    rcases hk with h | h <;> simp [baseLoHi, h]
  rcases Nat.lt_or_ge id.ratio 3 with hr | hr
  · interval_cases hr2 : id.ratio
    · rw [rootLoHi_ratio0 st pr id hr2, hb]
    · rw [rootLoHi_ratio1 st pr id hr2, if_neg (by simpa using hnw), hb]
    · rw [rootLoHi_ratio2 st pr id hr2, if_neg, hb]
      rintro ⟨-, hp⟩
      have := pvarOf_ne_zero_of_ne_fe id hnfe hp
      omega
  · unfold rootLoHi; simp only [show (2 : ℕ) ≤ 2 from le_refl _, if_true]
    rw [if_neg (by omega), if_neg (by omega), hb]

theorem y0_nonneg_of_root (st : Setup) (pr : Params) (id : ChartId) (y : Fin 5 → ℝ)
    (hy : InBoxR (rootBox st pr id) y) : 0 ≤ y 0 := by
  have := ((inBoxR_iff st pr id y).mp hy 0).1
  rw [show ((0 : Fin 5) : ℕ) = 0 from rfl, rootLoHi_zero] at this
  simpa using this

theorem y2_nonneg_of_root_cone (st : Setup) (pr : Params) (id : ChartId) (hk : isCone id = true)
    (hax : id.axis < 3) (y : Fin 5 → ℝ) (hy : InBoxR (rootBox st pr id) y) : 0 ≤ y 2 := by
  have hk' : id.kind = .cone ∨ id.kind = .mcone := by
    unfold isCone at hk; simpa using hk
  have := ((inBoxR_iff st pr id y).mp hy 2).1
  rw [show ((2 : Fin 5) : ℕ) = 2 from rfl, rootLoHi_two_cone st pr id hk' hax] at this
  simpa using this

/-- A witness leaf: u × c ≠ 0 on the root box, and the screened divided witness polynomials
are ≥ 0 on the leaf box. -/
def witnessLeafOk (st : Setup) (pr : Params) (id : ChartId) (V : Array KVec) (vk c : KVec) (box : Box) : Bool :=
  dOk st pr id c && boxOk (screened (witnessPolys (makeChart st id) id V vk c) (rootBox st pr id)) box

theorem witnessLeafOk_sound (st : Setup) (pr : Params) (id : ChartId) (hax : id.axis < 3) (V : Array KVec)
    (vk c : KVec) (box : Box) (h : witnessLeafOk st pr id V vk c box = true)
    (hrw : ∀ i, 0 ≤ (rootBox st pr id i).2) (hbw : ∀ i, 0 ≤ (box i).2)
    (y : Fin 5 → ℝ) (hyb : InBoxR box y) (hyr : InBoxR (rootBox st pr id) y) :
    rcross (rChartU st id y) (kv c) ≠ 0 ∧
      ∀ vj ∈ V, 0 ≤ witnessValue (rChartU st id y) (rChartW st id y) (kv vk) (kv c) (kv vj) := by
  simp only [witnessLeafOk, Bool.and_eq_true] at h
  refine ⟨dOk_sound st pr id c h.1 hrw y hyr, ?_⟩
  have hs := boxOk_sound hbw h.2 hyb
  have hall := screened_sound _ _ hrw y hyr hs
  have hnn := witnessPoly_nonneg (makeChart st id) id V vk c y (y0_nonneg_of_root st pr id y hyr)
    (fun hc => y2_nonneg_of_root_cone st pr id hc hax y hyr) hall
  intro vj hvj
  have := hnn vj hvj
  rwa [eval_chart_witnessPoly] at this

/-! ### Cone-region leaves (F_e charts) -/

def ivl (box : Box) (v : Fin 5) : ℚ × ℚ := ((box v).1, (box v).1 + (box v).2)

def mulIvl (a b : ℚ × ℚ) : ℚ × ℚ :=
  let p := [a.1 * b.1, a.1 * b.2, a.2 * b.1, a.2 * b.2]
  (p.foldr min (a.1 * b.1), p.foldr max (a.1 * b.1))

theorem le_mul_of_corners {a1 a2 b1 b2 x y m : ℝ} (hx : a1 ≤ x ∧ x ≤ a2) (hy : b1 ≤ y ∧ y ≤ b2)
    (h11 : m ≤ a1 * b1) (h12 : m ≤ a1 * b2) (h21 : m ≤ a2 * b1) (h22 : m ≤ a2 * b2) : m ≤ x * y := by
  rcases le_total 0 y with hy0 | hy0
  · have hxy : a1 * y ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
    rcases le_total 0 a1 with ha | ha
    · have : a1 * b1 ≤ a1 * y := mul_le_mul_of_nonneg_left hy.1 ha
      linarith
    · have : a1 * b2 ≤ a1 * y := mul_le_mul_of_nonpos_left hy.2 ha
      linarith
  · have hxy : a2 * y ≤ x * y := mul_le_mul_of_nonpos_right hx.2 hy0
    rcases le_total 0 a2 with ha | ha
    · have : a2 * b1 ≤ a2 * y := mul_le_mul_of_nonneg_left hy.1 ha
      linarith
    · have : a2 * b2 ≤ a2 * y := mul_le_mul_of_nonpos_left hy.2 ha
      linarith

theorem mul_le_of_corners {a1 a2 b1 b2 x y M : ℝ} (hx : a1 ≤ x ∧ x ≤ a2) (hy : b1 ≤ y ∧ y ≤ b2)
    (h11 : a1 * b1 ≤ M) (h12 : a1 * b2 ≤ M) (h21 : a2 * b1 ≤ M) (h22 : a2 * b2 ≤ M) : x * y ≤ M := by
  have := le_mul_of_corners (m := -M) (x := x) (y := -y) (b1 := -b2) (b2 := -b1) hx ⟨by linarith, by linarith⟩
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

theorem mem_mulIvl {a b : ℚ × ℚ} {x y : ℝ} (hx : (a.1 : ℝ) ≤ x ∧ x ≤ a.2) (hy : (b.1 : ℝ) ≤ y ∧ y ≤ b.2) :
    ((mulIvl a b).1 : ℝ) ≤ x * y ∧ x * y ≤ (mulIvl a b).2 := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [mulIvl, List.foldr_cons, List.foldr_nil] at *
  push_cast
  constructor
  · apply le_mul_of_corners hx hy
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  · apply mul_le_of_corners hx hy
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)

/-- The interval of the F_e chart's s_i over the box (after the ratio substitution). -/
def sRange (st : Setup) (id : ChartId) (box : Box) (i : Fin 3) : ℚ × ℚ :=
  let v : Fin 5 := ⟨2 + i, by omega⟩
  if id.ratio = 1 ∧ (List.range 3).any (fun j => !st.strong j && pvarOf id j = some (i : ℕ)) = true then
    mulIvl (ivl box 0) (ivl box v)
  else if id.ratio = 2 ∧ pvarOf id id.ratioCoord = some (i : ℕ) then
    let l := (id.z : ℚ) * (ivl box 0).1 + (ivl box v).1
    let h := (id.z : ℚ) * (ivl box 0).2 + (ivl box v).2
    if id.ratioSign then (l, h) else (-h, -l)
  else ivl box v

theorem mem_ivl {box : Box} {y : Fin 5 → ℝ} (hy : InBoxR box y) (v : Fin 5) :
    ((ivl box v).1 : ℝ) ≤ y v ∧ y v ≤ (ivl box v).2 := by
  obtain ⟨h1, h2⟩ := hy v
  simp only [ivl]; push_cast; exact ⟨h1, h2⟩

theorem sRange_sound (st : Setup) (id : ChartId) (box : Box) (y : Fin 5 → ℝ) (hy : InBoxR box y) (i : Fin 3) :
    ((sRange st id box i).1 : ℝ) ≤ rRatioVar st id y i ∧ rRatioVar st id y i ≤ (sRange st id box i).2 := by
  have hv : rpv y i = y ⟨2 + i, by omega⟩ := rpv_eq y i i.isLt
  have h0 := mem_ivl hy 0
  have hvv := mem_ivl hy ⟨2 + i, by omega⟩
  unfold sRange rRatioVar
  by_cases h1 : id.ratio = 1
  · by_cases hw : (List.range 3).any (fun j => !st.strong j && pvarOf id j = some (i : ℕ)) = true
    · rw [if_pos ⟨h1, hw⟩, if_pos h1, if_pos hw, hv]
      exact mem_mulIvl h0 hvv
    · rw [if_neg (fun h => hw h.2), if_neg (by rw [h1]; omega), if_pos h1, if_neg hw, hv]
      exact hvv
  · rw [if_neg (fun h => h1 h.1), if_neg h1]
    by_cases h2 : id.ratio = 2 ∧ pvarOf id id.ratioCoord = some (i : ℕ)
    · rw [if_pos h2, if_pos h2]
      have hz : (0 : ℝ) ≤ id.z := by positivity
      simp only
      rw [hv]
      split_ifs
      · push_cast; constructor <;> nlinarith [h0.1, h0.2, hvv.1, hvv.2]
      · push_cast; constructor <;> nlinarith [h0.1, h0.2, hvv.1, hvv.2]
    · rw [if_neg h2, if_neg h2, hv]; exact hvv

/-- |s − c| ≤ bound on the whole interval. -/
def within (r : ℚ × ℚ) (c bound : ℚ) : Bool := decide (max |r.1 - c| |r.2 - c| ≤ bound)

theorem within_sound {r : ℚ × ℚ} {c bound : ℚ} (h : within r c bound = true) {x : ℝ}
    (hx : (r.1 : ℝ) ≤ x ∧ x ≤ r.2) : |x - c| ≤ bound := by
  have hb := of_decide_eq_true h
  have h1 : |(r.1 : ℝ) - c| ≤ bound := by
    have := le_trans (le_max_left _ _) hb; exact_mod_cast this
  have h2 : |(r.2 : ℝ) - c| ≤ bound := by
    have := le_trans (le_max_right _ _) hb; exact_mod_cast this
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [hx.1, hx.2, h1.1, h1.2, h2.1, h2.2]

/-- An F_e box inside the cone region (identity cone, or the tie cone at (1, 0, 0)). -/
def coneOk (st : Setup) (pr : Params) (id : ChartId) (box : Box) : Bool :=
  let w (i : Fin 3) (c : ℚ) := within (sRange st id box i) c (pr.t0 * halfRange st i)
  decide (id.kind = .fe) && ((w 0 0 && w 1 0 && w 2 0) || (st.aniso && pr.tieCones && w 0 1 && w 1 0 && w 2 0))

theorem coneOk_sound (st : Setup) (pr : Params) (id : ChartId) (box : Box) (h : coneOk st pr id box = true)
    (y : Fin 5 → ℝ) (hy : InBoxR box y) :
    id.kind = .fe ∧ InConeRegion st pr (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2 := by
  simp only [coneOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hfe, h⟩ := h
  refine ⟨hfe, ?_⟩
  have hs : ∀ i : Fin 3, (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2 i = rRatioVar st id y i := by
    intro i; simp [rES, hfe]
  have hw : ∀ (i : Fin 3) (c : ℚ), within (sRange st id box i) c (pr.t0 * halfRange st i) = true →
      |rRatioVar st id y i - c| ≤ (pr.t0 : ℝ) * halfRange st i := by
    intro i c hc
    have := within_sound hc (sRange_sound st id box y hy i)
    push_cast at this; exact this
  unfold InConeRegion
  rcases h with ⟨⟨h0, h1⟩, h2⟩ | ⟨⟨⟨⟨han, htie⟩, h0⟩, h1⟩, h2⟩
  · left
    intro i
    rw [hs]
    fin_cases i
    · simpa using hw 0 0 h0
    · simpa using hw 1 0 h1
    · simpa using hw 2 0 h2
  · right
    refine ⟨han, htie, ?_, ?_, ?_⟩
    · rw [hs]; simpa using hw 0 1 h0
    · rw [hs]; simpa using hw 1 0 h1
    · rw [hs]; simpa using hw 2 0 h2

end Noperthedron.PentagonalHexecontahedron.Cap
