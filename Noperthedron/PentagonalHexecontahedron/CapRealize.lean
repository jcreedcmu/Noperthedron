module

public import Noperthedron.PentagonalHexecontahedron.CapFrame

@[expose] public section

/-!
# Realizing chart points (the ratio blow-ups)

`realize_ratio`: a point y₀ of a base chart's root box (no ratio substitution)
is, after the ratio blow-up of its strongly dominated weak coordinates, a point
y of one of the charts in `expandChart` with the same μ, τ, the same p₀ for
non-F_e kinds, and the same values of the substituted p variables
(`rRatioVar st id y k = rpv y₀ k`). Together with `rES_congr` the charts of
`expandChart b` realize every point of the base chart.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

def baseId (zOf : Kind × ℕ × ℕ × Bool → ℕ) (b : Kind × ℕ × ℕ × Bool) : ChartId :=
  ⟨b.1, b.2.1, b.2.2.1, b.2.2.2, 0, 0, true, zOf b⟩

/-- Real box membership with (lo, width) rational boxes. -/
abbrev InBoxR (box : Fin 5 → ℚ × ℚ) (y : Fin 5 → ℝ) : Prop := NPoly.InBox box y

theorem rpv_eq (y : Fin 5 → ℝ) (k : ℕ) (hk : k < 3) : rpv y k = y ⟨2 + k, by omega⟩ := by
  simp only [rpv]
  congr 1
  ext
  simp only
  omega

theorem pvarOf_lt (id : ChartId) (hax : id.axis < 3) {i k : ℕ} (hi : i < 3) (h : pvarOf id i = some k) :
    k < 3 := by
  obtain ⟨kind, side, axis, sign, ratio, rc, rs, z⟩ := id
  simp only at hax
  unfold pvarOf at h
  simp only at h
  split_ifs at h with h1 h2
  · cases h; exact hi
  · interval_cases i <;> interval_cases axis <;> simp_all [List.range_succ] <;> omega

/-- p index k carries a weak coordinate of the chart. -/
def IsWeakP (st : Setup) (id : ChartId) (k : ℕ) : Prop :=
  ∃ i < 3, st.strong i = false ∧ pvarOf id i = some k

open Classical in
theorem any_weak_iff (st : Setup) (id : ChartId) (k : ℕ) :
    (List.range 3).any (fun i => !st.strong i && pvarOf id i = some k) = true ↔ IsWeakP st id k := by
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq, IsWeakP]

open Classical in
theorem rRatioVar_inner (st : Setup) (id : ChartId) (h1 : id.ratio = 1) (y : Fin 5 → ℝ) (k : ℕ) :
    rRatioVar st id y k = if IsWeakP st id k then y 0 * rpv y k else rpv y k := by
  unfold rRatioVar
  simp only [h1, if_true]
  by_cases hw : IsWeakP st id k
  · rw [if_pos ((any_weak_iff st id k).mpr hw), if_pos hw]
  · rw [if_neg (fun h => hw ((any_weak_iff st id k).mp h)), if_neg hw]

theorem rRatioVar_outer (st : Setup) (id : ChartId) (h2 : id.ratio = 2) (y : Fin 5 → ℝ) (k : ℕ) :
    rRatioVar st id y k = if pvarOf id id.ratioCoord = some k then
      (if id.ratioSign then 1 else -1) * ((id.z : ℝ) * y 0 + rpv y k) else rpv y k := by
  unfold rRatioVar
  simp only [h2, show (2 : ℕ) ≠ 1 by norm_num, if_false, true_and]
  split_ifs <;> simp

theorem rRatioVar_none (st : Setup) (id : ChartId) (h0 : id.ratio = 0) (y : Fin 5 → ℝ) (k : ℕ) :
    rRatioVar st id y k = rpv y k := by
  unfold rRatioVar
  simp [h0]

theorem inBoxR_iff (st : Setup) (pr : Params) (id : ChartId) (y : Fin 5 → ℝ) :
    InBoxR (rootBox st pr id) y ↔
      ∀ v : Fin 5, ((rootLoHi st pr id v).1 : ℝ) ≤ y v ∧ y v ≤ (rootLoHi st pr id v).2 := by
  unfold InBoxR NPoly.InBox rootBox
  simp only
  constructor <;> intro h v <;> have := h v <;> push_cast at this ⊢ <;> constructor <;> linarith [this.1, this.2]

theorem pvarOf_ne_zero_of_ne_fe (id : ChartId) (h : id.kind ≠ .fe) {i k : ℕ} (hk : pvarOf id i = some k) :
    1 ≤ k := by
  unfold pvarOf at hk
  simp only [h, if_false] at hk
  split_ifs at hk
  cases hk; omega

/-- Weak p coordinates have symmetric base bounds (−h, h), h ≥ 0. -/
theorem weak_base_symm (st : Setup) (pr : Params) (id : ChartId) (hax : id.axis < 3) {k : ℕ}
    (hw : IsWeakP st id k) :
    k < 3 ∧ (baseLoHi st pr id.kind id.axis (2 + k)).1 = -(baseLoHi st pr id.kind id.axis (2 + k)).2 ∧
      0 ≤ (baseLoHi st pr id.kind id.axis (2 + k)).2 := by
  obtain ⟨i, hi, -, hk⟩ := hw
  have hk3 := pvarOf_lt id hax hi hk
  refine ⟨hk3, ?_⟩
  by_cases hfe : id.kind = .fe
  · interval_cases k <;> simp [baseLoHi, hfe]
  · have h1 := pvarOf_ne_zero_of_ne_fe id hfe hk
    rcases hkind : id.kind with _ | _ | _ | _
    · exact absurd hkind hfe
    all_goals (interval_cases k <;> simp [baseLoHi])

open Classical in
theorem rootLoHi_ratio1 (st : Setup) (pr : Params) (id : ChartId) (h1 : id.ratio = 1) (v : ℕ) :
    rootLoHi st pr id v = if 2 ≤ v ∧ IsWeakP st id (v - 2) then (-(id.z : ℚ), (id.z : ℚ))
      else baseLoHi st pr id.kind id.axis v := by
  unfold rootLoHi
  by_cases h2 : 2 ≤ v
  · by_cases hw : IsWeakP st id (v - 2)
    · rw [if_pos h2, if_pos ⟨h1, (any_weak_iff st id _).mpr hw⟩, if_pos ⟨h2, hw⟩]
    · have hany : ¬ (id.ratio = 1 ∧ (List.range 3).any (fun i => !st.strong i && pvarOf id i = some (v - 2)) = true) :=
        fun h => hw ((any_weak_iff st id _).mp h.2)
      rw [if_pos h2, if_neg hany, if_neg (by rw [h1]; omega), if_neg (fun h => hw h.2)]
  · rw [if_neg h2, if_neg (fun h => h2 h.1)]

open Classical in
theorem rootLoHi_ratio2 (st : Setup) (pr : Params) (id : ChartId) (h2' : id.ratio = 2) (v : ℕ) :
    rootLoHi st pr id v = if 2 ≤ v ∧ pvarOf id id.ratioCoord = some (v - 2) then
      (0, (baseLoHi st pr id.kind id.axis v).2) else baseLoHi st pr id.kind id.axis v := by
  unfold rootLoHi
  by_cases h2 : 2 ≤ v
  · rw [if_pos h2, if_neg (by rw [h2']; omega)]
    by_cases hp : pvarOf id id.ratioCoord = some (v - 2)
    · rw [if_pos ⟨h2', hp⟩, if_pos ⟨h2, hp⟩]
    · rw [if_neg (fun h => hp h.2), if_neg (fun h => hp h.2)]
  · rw [if_neg h2, if_neg (fun h => h2 h.1)]

theorem rootLoHi_ratio0 (st : Setup) (pr : Params) (id : ChartId) (h0 : id.ratio = 0) (v : ℕ) :
    rootLoHi st pr id v = baseLoHi st pr id.kind id.axis v := by
  unfold rootLoHi
  split_ifs with h2 ha hb <;> first | rfl | (exfalso; rw [h0] at ha; exact absurd ha.1 (by norm_num)) |
    (exfalso; rw [h0] at hb; exact absurd hb.1 (by norm_num))

theorem mem_expand_inner (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ)
    (b : Kind × ℕ × ℕ × Bool) (hr : (pr.ratioOn && (b.1 = .fe || st.strong b.2.2.1)) = true) :
    ({ baseId zOf b with ratio := 1 } : ChartId) ∈ expandChart st pr zOf b := by
  obtain ⟨kind, side, axis, sign⟩ := b
  simp only at hr
  simp only [expandChart, hr, if_true, baseId]
  exact List.mem_cons_self

theorem mem_expand_outer (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ)
    (b : Kind × ℕ × ℕ × Bool) (hr : (pr.ratioOn && (b.1 = .fe || st.strong b.2.2.1)) = true)
    {i k : ℕ} (hi : i < 3) (hs : st.strong i = false) (hp : pvarOf (baseId zOf b) i = some k) (sg : Bool) :
    ({ baseId zOf b with ratio := 2, ratioCoord := i, ratioSign := sg } : ChartId) ∈ expandChart st pr zOf b := by
  obtain ⟨kind, side, axis, sign⟩ := b
  simp only at hr
  simp only [expandChart, hr, if_true]
  apply List.mem_cons_of_mem
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  have hsome : (pvarOf (⟨kind, side, axis, sign, 0, 0, true, zOf (kind, side, axis, sign)⟩ : ChartId) i).isSome
      = true := by
    have : pvarOf (baseId zOf (kind, side, axis, sign)) i = some k := hp
    simp only [baseId] at this
    rw [this]; rfl
  rw [if_pos (by simp [hs, hsome])]
  cases sg
  · simp [baseId]
  · simp [baseId]

open Classical in
/-- The ratio blow-up realizes every point of the base chart. -/
theorem realize_ratio (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ)
    (b : Kind × ℕ × ℕ × Bool) (hax : b.2.2.1 < 3) (hz : 0 < zOf b)
    (y₀ : Fin 5 → ℝ) (hy₀ : InBoxR (rootBox st pr (baseId zOf b)) y₀) (hμ : 0 ≤ y₀ 0) :
    ∃ id ∈ expandChart st pr zOf b, id.kind = b.1 ∧ id.side = b.2.1 ∧ id.axis = b.2.2.1 ∧
      id.sign = b.2.2.2 ∧ ∃ y, InBoxR (rootBox st pr id) y ∧ y 0 = y₀ 0 ∧ y 1 = y₀ 1 ∧
        (∀ k < 3, rRatioVar st id y k = rpv y₀ k) ∧ (b.1 ≠ .fe → rpv y 0 = rpv y₀ 0) := by
  set base := baseId zOf b with hbase
  have hbk : base.kind = b.1 := rfl
  have hba : base.axis = b.2.2.1 := rfl
  have hy₀' := (inBoxR_iff st pr base y₀).mp hy₀
  have hb0 : ∀ v : Fin 5, ((baseLoHi st pr b.1 b.2.2.1 v).1 : ℝ) ≤ y₀ v ∧
      y₀ v ≤ (baseLoHi st pr b.1 b.2.2.1 v).2 := by
    intro v; have := hy₀' v; rwa [rootLoHi_ratio0 st pr base rfl] at this
  have hZ : (0 : ℝ) < (zOf b : ℝ) := by exact_mod_cast hz
  -- Coordinates of y in terms of rpv.
  have hcoord : ∀ (y : Fin 5 → ℝ) (k : ℕ) (hk : k < 3), rpv y k = y ⟨2 + k, by omega⟩ := rpv_eq
  by_cases hr : (pr.ratioOn && (b.1 = .fe || st.strong b.2.2.1)) = true
  swap
  · -- No ratio blow-up: the base chart itself.
    refine ⟨base, ?_, rfl, rfl, rfl, rfl, y₀, hy₀, rfl, rfl, ?_, fun _ => rfl⟩
    · obtain ⟨kind, side, axis, sign⟩ := b
      simp only at hr
      simp only [expandChart, Bool.not_eq_true] at hr ⊢
      simp [hr, base, baseId]
    · intro k _; exact rRatioVar_none st base rfl y₀ k
  have hweak : ∀ (id : ChartId), id.kind = b.1 → id.axis = b.2.2.1 → ∀ k,
      IsWeakP st id k ↔ IsWeakP st base k := by
    intro id hk ha k
    simp only [IsWeakP, pvarOf, hk, ha, base, baseId]
  by_cases hall : ∀ k, IsWeakP st base k → |rpv y₀ k| ≤ (zOf b : ℝ) * y₀ 0
  · -- Inner chart.
    let id1 : ChartId := { base with ratio := 1 }
    let y : Fin 5 → ℝ := fun j => if 2 ≤ (j : ℕ) ∧ IsWeakP st base ((j : ℕ) - 2) then rpv y₀ ((j : ℕ) - 2) / y₀ 0
      else y₀ j
    have hval : ∀ k, IsWeakP st base k → y₀ 0 * (rpv y₀ k / y₀ 0) = rpv y₀ k := by
      intro k hk
      rcases eq_or_lt_of_le hμ with h0 | hpos
      · have := hall k hk
        rw [← h0, mul_zero] at this
        rw [abs_nonpos_iff.mp this]; simp
      · field_simp
    have hy0 : y 0 = y₀ 0 := by simp [y]
    have hy1 : y 1 = y₀ 1 := by simp [y]
    have hyk : ∀ k (hk : k < 3), rpv y k = if IsWeakP st base k then rpv y₀ k / y₀ 0 else rpv y₀ k := by
      intro k hk
      rw [hcoord y k hk]
      simp only [y, show (2 ≤ 2 + k) from by omega, true_and, Nat.add_sub_cancel_left]
      split_ifs
      · rfl
      · exact (hcoord y₀ k hk).symm
    refine ⟨id1, mem_expand_inner st pr zOf b hr, rfl, rfl, rfl, rfl, y, ?_, hy0, hy1, ?_, ?_⟩
    · rw [inBoxR_iff]
      intro v
      rw [rootLoHi_ratio1 st pr id1 rfl]
      by_cases hv : 2 ≤ (v : ℕ) ∧ IsWeakP st base ((v : ℕ) - 2)
      · rw [if_pos ⟨hv.1, (hweak id1 rfl rfl _).mpr hv.2⟩]
        have hyv : y v = rpv y₀ ((v : ℕ) - 2) / y₀ 0 := by simp only [y]; rw [if_pos hv]
        rw [hyv]
        have hb := hall _ hv.2
        have hz1 : ((id1.z : ℚ) : ℝ) = (zOf b : ℝ) := by simp [id1, base, baseId]
        simp only [Rat.cast_neg, hz1]
        rcases eq_or_lt_of_le hμ with h0 | hpos
        · rw [← h0, div_zero]; constructor <;> linarith
        · rw [← abs_le, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]; exact hb
      · rw [if_neg (fun h => hv ⟨h.1, (hweak id1 rfl rfl _).mp h.2⟩)]
        have hyv : y v = y₀ v := by simp only [y]; rw [if_neg hv]
        rw [hyv]
        exact hb0 v
    · intro k hk
      rw [rRatioVar_inner st id1 rfl y k, hyk k hk]
      by_cases hw : IsWeakP st base k
      · rw [if_pos ((hweak id1 rfl rfl k).mpr hw), if_pos hw, hy0]; exact hval k hw
      · rw [if_neg (fun h => hw ((hweak id1 rfl rfl k).mp h)), if_neg hw]
    · intro hfe
      rw [hyk 0 (by norm_num)]
      have : ¬ IsWeakP st base 0 := by
        rintro ⟨i, -, -, hi⟩
        have := pvarOf_ne_zero_of_ne_fe base hfe hi
        omega
      rw [if_neg this]
  · -- Outer chart at a weak coordinate whose value exceeds Z μ.
    push Not at hall
    obtain ⟨k, hkw, hbig⟩ := hall
    obtain ⟨hk3, hsymm, hhi⟩ := weak_base_symm st pr base hax hkw
    obtain ⟨i, hi3, hstrong, hpk⟩ := hkw
    let sg : Bool := decide (0 ≤ rpv y₀ k)
    let id2 : ChartId := { base with ratio := 2, ratioCoord := i, ratioSign := sg }
    let y : Fin 5 → ℝ := fun j => if (j : ℕ) = 2 + k then |rpv y₀ k| - (zOf b : ℝ) * y₀ 0 else y₀ j
    have hpk2 : pvarOf id2 id2.ratioCoord = some k := hpk
    have hy0 : y 0 = y₀ 0 := by
      simp only [y]; rw [if_neg (by simp only [Fin.val_zero]; omega)]
    have hy1 : y 1 = y₀ 1 := by
      simp only [y]; rw [if_neg (by simp only [Fin.val_one]; omega)]
    have hyk : ∀ k' (hk' : k' < 3), rpv y k' = if k' = k then |rpv y₀ k| - (zOf b : ℝ) * y₀ 0 else rpv y₀ k' := by
      intro k' hk'
      rw [hcoord y k' hk', hcoord y₀ k' hk']
      simp only [y]
      by_cases h : k' = k
      · rw [if_pos (by simp [h]), if_pos h]
      · rw [if_neg (by simp; omega), if_neg h]
    refine ⟨id2, mem_expand_outer st pr zOf b hr hi3 hstrong hpk sg, rfl, rfl, rfl, rfl, y, ?_, hy0, hy1, ?_, ?_⟩
    · rw [inBoxR_iff]
      intro v
      rw [rootLoHi_ratio2 st pr id2 rfl]
      by_cases hv : (v : ℕ) = 2 + k
      · rw [if_pos ⟨by omega, by rw [hpk2]; congr 1; omega⟩]
        have hyv : y v = |rpv y₀ k| - (zOf b : ℝ) * y₀ 0 := by simp only [y]; rw [if_pos hv]
        rw [hyv]
        have hbv := hb0 v
        have hvk : (⟨2 + k, by omega⟩ : Fin 5) = v := Fin.ext hv.symm
        have hrv : rpv y₀ k = y₀ v := by rw [hcoord y₀ k hk3, hvk]
        rw [show (v : ℕ) = 2 + k from hv] at hbv
        rw [← hrv] at hbv
        have hsy : ((baseLoHi st pr b.1 b.2.2.1 (2 + k)).1 : ℝ) = -((baseLoHi st pr b.1 b.2.2.1 (2 + k)).2 : ℝ) := by
          exact_mod_cast hsymm
        have habs : |rpv y₀ k| ≤ (baseLoHi st pr b.1 b.2.2.1 (2 + k)).2 := by
          rw [abs_le]; constructor <;> linarith [hbv.1, hbv.2]
        have hid2 : id2.kind = b.1 ∧ id2.axis = b.2.2.1 := ⟨rfl, rfl⟩
        rw [hid2.1, hid2.2, show (v : ℕ) = 2 + k from hv]
        simp only [Rat.cast_zero]
        constructor
        · linarith
        · nlinarith [mul_nonneg hZ.le hμ]
      · rw [if_neg (fun h => hv (by rw [hpk2] at h; cases h.2; omega))]
        have hyv : y v = y₀ v := by simp only [y]; rw [if_neg hv]
        rw [hyv]
        exact hb0 v
    · intro k' hk'
      rw [rRatioVar_outer st id2 rfl y k', hpk2, hyk k' hk']
      by_cases hkk : k = k'
      · subst hkk
        rw [if_pos rfl, if_pos rfl, hy0]
        show (if sg then (1 : ℝ) else -1) * ((zOf b : ℝ) * y₀ 0 + (|rpv y₀ k| - (zOf b : ℝ) * y₀ 0)) = _
        by_cases hpos : 0 ≤ rpv y₀ k
        · have : sg = true := by simp [sg, hpos]
          rw [this, abs_of_nonneg hpos]; simp
        · have : sg = false := by simp [sg, hpos]
          rw [this, abs_of_neg (lt_of_not_ge hpos)]; simp
      · rw [if_neg (fun h => hkk (Option.some.inj h)), if_neg (Ne.symm hkk)]
    · intro hfe
      have := pvarOf_ne_zero_of_ne_fe base hfe hpk
      rw [hyk 0 (by norm_num), if_neg (by omega)]

end Noperthedron.PentagonalHexecontahedron.Cap
