module

public import Noperthedron.PentagonalHexecontahedron.CapRealize

@[expose] public section

/-!
# The cap domain is covered by the charts

`cap_cover`: for an orthonormal frame (x, e₁, e₂), every pose with view
u = x + t₁ e₁ + t₂ e₂ (|tᵢ| ≤ μ₀) and Cayley vector w with |w| ≤ wmax
(wmax ≤ 2 μ₀, wmax ≤ S μ₀²) is the image (rChartU, rChartW) of a point of
the root box of a chart in `chartList`; an F_e chart is used only outside the
cone region (which the cone charts cover).
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

theorem rdot_sq_le (w v : Fin 3 → ℝ) : rdot w v ^ 2 ≤ rdot w w * rdot v v := by
  simp only [rdot]
  nlinarith [sq_nonneg (w 0 * v 1 - w 1 * v 0), sq_nonneg (w 0 * v 2 - w 2 * v 0),
    sq_nonneg (w 1 * v 2 - w 2 * v 1)]

theorem rdot_self_nonneg (w : Fin 3 → ℝ) : 0 ≤ rdot w w := by
  simp only [rdot]; nlinarith [mul_self_nonneg (w 0), mul_self_nonneg (w 1), mul_self_nonneg (w 2)]

/-- The F_e chart's cone region (identity cone; tie cone at (1, 0, 0) for ux). -/
def InConeRegion (st : Setup) (pr : Params) (s : Fin 3 → ℝ) : Prop :=
  (∀ i : Fin 3, |s i| ≤ pr.t0 * halfRange st i) ∨
    (st.aniso = true ∧ pr.tieCones = true ∧ |s 0 - 1| ≤ pr.t0 * halfRange st 0 ∧
      |s 1| ≤ pr.t0 * halfRange st 1 ∧ |s 2| ≤ pr.t0 * halfRange st 2)

/-- The frame of a cap (real values orthonormal). -/
def FrameOK (st : Setup) : Prop := Orthonormal3 (kv st.e1) (kv st.e2) (kv st.x)

/-- The side's (A, B) as real vectors in terms of (e₁, e₂). -/
theorem frameAB_val (st : Setup) (side : ℕ) (hside : side < 4) :
    kv (st.frameAB side).1 = (sideA side).1 • kv st.e1 + (sideA side).2 • kv st.e2 ∧
      kv (st.frameAB side).2 = (sideB side).1 • kv st.e1 + (sideB side).2 • kv st.e2 := by
  interval_cases side <;> simp [Setup.frameAB, sideA, sideB, kval_kneg] <;> funext i <;> simp

theorem side_props (st : Setup) (hF : FrameOK st) (side : ℕ) (hside : side < 4) (τ : ℝ) :
    let a := kv (st.frameAB side).1 + τ • kv (st.frameAB side).2
    rdot (kv st.x) a = 0 ∧ rdot a a = 1 + τ ^ 2 := by
  obtain ⟨h11, h22, hxx, h12, h1x, h2x⟩ := hF
  obtain ⟨hA, hB⟩ := frameAB_val st side hside
  simp only
  rw [hA, hB]
  have lin : ∀ (p q r : Fin 3 → ℝ) (α β γ δ : ℝ),
      rdot (α • p + β • q) (γ • p + δ • q) = α * γ * rdot p p + (α * δ + β * γ) * rdot p q + β * δ * rdot q q := by
    intro p q r α β γ δ; simp only [rdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  constructor
  · simp only [rdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1x h2x ⊢
    interval_cases side <;> simp [sideA, sideB] <;>
      first
      | linear_combination h1x + τ * h2x
      | linear_combination -h1x + τ * h2x
      | linear_combination h2x + τ * h1x
      | linear_combination -h2x + τ * h1x
  · simp only [rdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h11 h22 h12 ⊢
    interval_cases side <;> simp [sideA, sideB] <;>
      first
      | linear_combination h11 + τ ^ 2 * h22 + 2 * τ * h12
      | linear_combination h11 + τ ^ 2 * h22 - 2 * τ * h12
      | linear_combination h22 + τ ^ 2 * h11 + 2 * τ * h12
      | linear_combination h22 + τ ^ 2 * h11 - 2 * τ * h12

theorem mem_chartList (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ)
    {b : Kind × ℕ × ℕ × Bool} (hb : b ∈ baseCharts pr) {id : ChartId} (hid : id ∈ expandChart st pr zOf b) :
    id ∈ chartList st pr zOf :=
  List.mem_flatMap.mpr ⟨b, hb, hid⟩

theorem fe_mem_base (pr : Params) {side : ℕ} (h : side < 4) : (Kind.fe, side, 0, true) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  exact ⟨side, h, List.mem_cons_self⟩

theorem face_mem_base (pr : Params) {side axis : ℕ} (h : side < 4) (ha : axis < 3) (sg : Bool) :
    (Kind.face, side, axis, sg) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  refine ⟨side, h, List.mem_cons_of_mem _ ?_⟩
  rw [List.mem_flatMap]
  refine ⟨axis, List.mem_range.mpr ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨sg, by cases sg <;> simp, ?_⟩
  simp

theorem cone_mem_base (pr : Params) {side axis : ℕ} (h : side < 4) (ha : axis < 3) (sg : Bool) :
    (Kind.cone, side, axis, sg) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  refine ⟨side, h, List.mem_cons_of_mem _ ?_⟩
  rw [List.mem_flatMap]
  refine ⟨axis, List.mem_range.mpr ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨sg, by cases sg <;> simp, ?_⟩
  simp

theorem mcone_mem_base (pr : Params) (ht : pr.tieCones = true) {side axis : ℕ} (h : side < 4) (ha : axis < 3)
    (sg : Bool) : (Kind.mcone, side, axis, sg) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  refine ⟨side, h, List.mem_cons_of_mem _ ?_⟩
  rw [List.mem_flatMap]
  refine ⟨axis, List.mem_range.mpr ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨sg, by cases sg <;> simp, ?_⟩
  simp [ht]

/-- The chart's view in terms of its (e, μ, τ). -/
theorem rChartU_eq (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) :
    rChartU st id y = kv st.x + (y 0 * (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).1) •
      (kv (st.frameAB id.side).1 + y 1 • kv (st.frameAB id.side).2) := rfl

theorem rChartW_eq (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) :
    rChartW st id y =
      let s := (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2
      let a := kv (st.frameAB id.side).1 + y 1 • kv (st.frameAB id.side).2
      if st.aniso then (y 0 * s 0) • rcross (kv st.x) a + ((y 0 * y 0) * s 1) • a + ((y 0 * y 0) * s 2) • kv st.x
      else (y 0 * s 0) • kv st.e1 + (y 0 * s 1) • kv st.e2 + ((y 0 * y 0) * s 2) • kv st.x := rfl

theorem range_pos (st : Setup) (hS : 2 ≤ st.strongScale) (i : ℕ) : (2 : ℝ) ≤ st.range i := by
  unfold Setup.range; split_ifs <;> [exact_mod_cast hS; norm_num]

theorem halfRange_pos (st : Setup) (hS : 2 ≤ st.strongScale) (i : ℕ) : (1 : ℝ) ≤ halfRange st i := by
  unfold halfRange
  have h : (2 : ℤ) ≤ (st.range i : ℤ) := by exact_mod_cast (show 2 ≤ st.range i by
    unfold Setup.range; split_ifs <;> omega)
  have : (1 : ℤ) ≤ (st.range i : ℤ) / 2 := by omega
  exact_mod_cast this

/-- The covering of the cap domain by the charts. -/
theorem cap_cover (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ) (hz : ∀ b, 0 < zOf b)
    (hF : FrameOK st) (hS : 2 ≤ st.strongScale) (ht0 : 0 ≤ (pr.t0 : ℝ))
    (wmax : ℝ) (hw0 : 0 ≤ wmax) (hw1 : wmax ≤ 2 * pr.mu0) (hw2 : wmax ≤ st.strongScale * (pr.mu0 : ℝ) ^ 2)
    (t₁ t₂ : ℝ) (ht₁ : |t₁| ≤ pr.mu0) (ht₂ : |t₂| ≤ pr.mu0) (w : Fin 3 → ℝ) (hw : rdot w w ≤ wmax ^ 2) :
    ∃ id ∈ chartList st pr zOf, ∃ y, InBoxR (rootBox st pr id) y ∧
      rChartU st id y = kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 ∧ rChartW st id y = w ∧
      (id.kind = .fe → ¬ InConeRegion st pr (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2) := by
  obtain ⟨side, hside, m, τ, hm, hτ, ht1', ht2'⟩ := view_side t₁ t₂
  set A := (st.frameAB side).1
  set B := (st.frameAB side).2
  set a := kv A + τ • kv B
  obtain ⟨hxa, haa⟩ := side_props st hF side hside τ
  have hm0 : 0 ≤ m := by rw [hm]; exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hm1 : m ≤ pr.mu0 := by rw [hm]; exact max_le ht₁ ht₂
  have hμ0nn : (0 : ℝ) ≤ pr.mu0 := le_trans hm0 hm1
  -- The view.
  have hview : ∀ μ e : ℝ, μ * e = m → kv st.x + (μ * e) • a = kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 := by
    intro μ e hme
    obtain ⟨hA, hB⟩ := frameAB_val st side hside
    rw [hme]
    funext k
    simp only [a, A, B, hA, hB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht1', ht2']; ring
  -- The weighted coordinates.
  have hwn : Real.sqrt (rdot w w) ≤ wmax := by
    rw [Real.sqrt_le_left hw0]; exact hw
  have haa1 : 1 ≤ rdot a a := by rw [haa]; nlinarith [sq_nonneg τ]
  have hcs : ∀ v : Fin 3 → ℝ, |rdot w v| ≤ Real.sqrt (rdot w w) * Real.sqrt (rdot v v) := by
    intro v
    rw [← Real.sqrt_mul (rdot_self_nonneg w), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (rdot_sq_le w v)
  let wt : Fin 3 → ℕ := fun i => if st.aniso then (if (i : ℕ) = 0 then 1 else 2) else (if (i : ℕ) = 2 then 2 else 1)
  let ω : Fin 3 → ℝ := fun i =>
    if st.aniso then ![rdot w (rcross (kv st.x) a) / rdot a a, rdot w a / rdot a a, rdot w (kv st.x)] i
    else ![rdot w (kv st.e1), rdot w (kv st.e2), rdot w (kv st.x)] i
  have hwt : ∀ i, wt i = 1 ∨ wt i = 2 := by intro i; simp only [wt]; split_ifs <;> simp
  have hR : ∀ i : Fin 3, (0 : ℝ) < (st.range i : ℝ) := fun i => by linarith [range_pos st hS i]
  have hrange : ∀ i : Fin 3, (st.range i : ℝ) = if wt i = 1 then 2 else st.strongScale := by
    intro i
    by_cases han : st.aniso = true <;> fin_cases i <;> simp [wt, Setup.range, Setup.strong, han]
  -- The six coordinate bounds by |w| ≤ wmax.
  obtain ⟨h11, h22, hxx, h12, h1x, h2x⟩ := hF
  have hun : ∀ e : Fin 3 → ℝ, rdot e e = 1 → |rdot w e| ≤ wmax := by
    intro e he
    have hc := hcs e
    rw [he, Real.sqrt_one, mul_one] at hc
    linarith
  have hpos : 0 < rdot a a := by linarith
  have hsq : Real.sqrt (rdot a a) ≤ rdot a a := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hdiv : ∀ v : Fin 3 → ℝ, rdot v v = rdot a a → |rdot w v / rdot a a| ≤ wmax := by
    intro v hv
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hc := hcs v
    rw [hv] at hc
    calc |rdot w v| ≤ Real.sqrt (rdot w w) * Real.sqrt (rdot a a) := hc
      _ ≤ wmax * rdot a a := mul_le_mul hwn hsq (Real.sqrt_nonneg _) hw0
  have hcc : rdot (rcross (kv st.x) a) (rcross (kv st.x) a) = rdot a a := by
    rw [rdot_rcross_rcross, hxx, hxa]; ring
  have hωb : ∀ i, |ω i| ≤ (st.range i : ℝ) * (pr.mu0 : ℝ) ^ wt i := by
    intro i
    have hle : |ω i| ≤ wmax := by
      by_cases han : st.aniso = true
      · fin_cases i
        · show |(if st.aniso then _ else _)| ≤ _
          rw [if_pos han]; exact hdiv _ hcc
        · show |(if st.aniso then _ else _)| ≤ _
          rw [if_pos han]; exact hdiv _ rfl
        · show |(if st.aniso then _ else _)| ≤ _
          rw [if_pos han]; exact hun _ hxx
      · fin_cases i
        · show |(if st.aniso then _ else _)| ≤ _
          rw [if_neg han]; exact hun _ h11
        · show |(if st.aniso then _ else _)| ≤ _
          rw [if_neg han]; exact hun _ h22
        · show |(if st.aniso then _ else _)| ≤ _
          rw [if_neg han]; exact hun _ hxx
    rw [hrange i]
    split_ifs with h1
    · rw [h1, pow_one]; push_cast; linarith
    · have h2 : wt i = 2 := by rcases hwt i with h | h; exact absurd h h1; exact h
      rw [h2]; linarith
  obtain ⟨μ, e, sv, hμ0, hμ1, he0, he1, hme, hωs, hcase⟩ :=
    weighted_cube wt hwt (fun i => (st.range i : ℝ)) hR pr.mu0 m hm0 hm1 ω hωb
  -- Closing the view and the Cayley vector for any chart point with these coordinates.
  have hU : ∀ (id : ChartId) (y : Fin 5 → ℝ), id.side = side → y 0 = μ → y 1 = τ →
      (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).1 = e →
      rChartU st id y = kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 := by
    intro id y hs h0 h1 he
    rw [rChartU_eq, he, h0, h1, hs]
    exact hview μ e hme.symm
  have hωv : ∀ i, ω i = μ ^ wt i * sv i := fun i => (hωs i).1
  have hW : ∀ (id : ChartId) (y : Fin 5 → ℝ), id.side = side → y 0 = μ → y 1 = τ →
      (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2 = sv → rChartW st id y = w := by
    intro id y hs h0 h1 hsv
    rw [rChartW_eq]
    simp only []
    rw [hsv, h0, h1, hs]
    by_cases han : st.aniso = true
    · rw [if_pos han]
      have hd := decomp_aniso hxx hxa hpos w
      have e0 := hωv 0; have e1 := hωv 1; have e2 := hωv 2
      simp only [ω, wt, if_pos han] at e0 e1 e2
      simp at e0 e1 e2
      conv_rhs => rw [hd]
      rw [e0, e1, e2]
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [if_neg han]
      have hd := decomp_orthonormal ⟨h11, h22, hxx, h12, h1x, h2x⟩ w
      have e0 := hωv 0; have e1 := hωv 1; have e2 := hωv 2
      simp only [ω, wt, if_neg han] at e0 e1 e2
      simp at e0 e1 e2
      conv_rhs => rw [hd]
      rw [e0, e1, e2]
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hsb : ∀ i : Fin 3, |sv i| ≤ st.range i := fun i => (hωs i).2
  have hhalf : ∀ i : Fin 3, (0 : ℝ) < 2 * (halfRange st i : ℝ) := fun i => by
    linarith [halfRange_pos st hS i]
  -- Sign of a unit coordinate.
  have hsgn : ∀ (x : ℝ), |x| = 1 → x = (if decide (0 ≤ x) then 1 else -1) := by
    intro x hx
    by_cases h : 0 ≤ x
    · simp only [h, decide_true, if_true]; rw [abs_of_nonneg h] at hx; exact hx
    · simp only [h, decide_false, Bool.false_eq_true, if_false]; rw [abs_of_neg (lt_of_not_ge h)] at hx; linarith
  have hμ1' : μ ≤ (pr.mu0 : ℝ) := hμ1
  rcases hcase with he | ⟨k, hk⟩
  · -- The F_e face (e = 1).
    by_cases hc1 : ∀ i : Fin 3, |sv i| ≤ pr.t0 * halfRange st i
    · obtain ⟨t, σ, k, htn, htt, hσk, hσ, hseq⟩ := cone_decomp (fun i => 2 * (halfRange st i : ℝ)) hhalf pr.t0 0 sv
        (by intro i; have := hc1 i; simp only [Pi.zero_apply, sub_zero]; linarith)
      obtain ⟨id, hid, hk', hsd, y, hy, hy0, hy1, hres⟩ := realize_cone st pr zOf .cone (Or.inl rfl) side k k.isLt
        (decide (0 ≤ σ k)) (hz _) μ τ t hμ0 hμ1' hτ htn htt σ hσ
        (fun i hi => by rw [show i = k from Fin.ext hi]; exact hsgn _ hσk) A B
      refine ⟨id, mem_chartList st pr zOf (cone_mem_base pr hside k.isLt _) hid, y, hy, ?_, ?_, ?_⟩
      · exact hU id y hsd hy0 hy1 (by rw [hsd, hres, he])
      · apply hW id y hsd hy0 hy1
        rw [hsd, hres]
        funext i
        rw [hseq i]
        simp [rCenter]
      · intro hfe; rw [hk'] at hfe; exact absurd hfe (by decide)
    · by_cases hc2 : st.aniso = true ∧ pr.tieCones = true ∧ |sv 0 - 1| ≤ pr.t0 * halfRange st 0 ∧
          |sv 1| ≤ pr.t0 * halfRange st 1 ∧ |sv 2| ≤ pr.t0 * halfRange st 2
      · obtain ⟨han, htie, hb0, hb1, hb2⟩ := hc2
        obtain ⟨t, σ, k, htn, htt, hσk, hσ, hseq⟩ := cone_decomp (fun i => 2 * (halfRange st i : ℝ)) hhalf pr.t0
          ![1, 0, 0] sv (by
            intro i
            fin_cases i
            · simp; linarith
            · simp; linarith
            · simp; linarith)
        obtain ⟨id, hid, hk', hsd, y, hy, hy0, hy1, hres⟩ := realize_cone st pr zOf .mcone (Or.inr rfl) side k
          k.isLt (decide (0 ≤ σ k)) (hz _) μ τ t hμ0 hμ1' hτ htn htt σ hσ
          (fun i hi => by rw [show i = k from Fin.ext hi]; exact hsgn _ hσk) A B
        refine ⟨id, mem_chartList st pr zOf (mcone_mem_base pr htie hside k.isLt _) hid, y, hy, ?_, ?_, ?_⟩
        · exact hU id y hsd hy0 hy1 (by rw [hsd, hres, he])
        · apply hW id y hsd hy0 hy1
          rw [hsd, hres]
          funext i
          rw [hseq i]
          fin_cases i <;> simp [rCenter, han] <;> ring
        · intro hfe; rw [hk'] at hfe; exact absurd hfe (by decide)
      · obtain ⟨id, hid, hk', hsd, y, hy, hy0, hy1, hres⟩ :=
          realize_fe st pr zOf side (hz _) μ τ hμ0 hμ1' hτ sv hsb A B
        refine ⟨id, mem_chartList st pr zOf (fe_mem_base pr hside) hid, y, hy, ?_, ?_, ?_⟩
        · exact hU id y hsd hy0 hy1 (by rw [hsd, hres, he])
        · exact hW id y hsd hy0 hy1 (by rw [hsd, hres])
        · intro _ hcone
          rw [hsd, hres] at hcone
          rcases hcone with h | h
          · exact hc1 h
          · exact hc2 h
  · -- A coordinate face: |s_k| = R_k.
    have hsk : sv k = (if decide (0 ≤ sv k) then 1 else -1) * (st.range k : ℝ) := by
      by_cases h : 0 ≤ sv k
      · simp only [h, decide_true, if_true, one_mul]; rw [abs_of_nonneg h] at hk; exact hk
      · simp only [h, decide_false, Bool.false_eq_true, if_false]; rw [abs_of_neg (lt_of_not_ge h)] at hk; linarith
    obtain ⟨id, hid, hk', hsd, y, hy, hy0, hy1, hres⟩ := realize_face st pr zOf side k k.isLt (decide (0 ≤ sv k))
      (hz _) μ τ e hμ0 hμ1' hτ he0 he1 sv hsb (fun i hi => by rw [show i = k from Fin.ext hi]; exact hsk) A B
    refine ⟨id, mem_chartList st pr zOf (face_mem_base pr hside k.isLt _) hid, y, hy, ?_, ?_, ?_⟩
    · exact hU id y hsd hy0 hy1 (by rw [hsd, hres])
    · exact hW id y hsd hy0 hy1 (by rw [hsd, hres])
    · intro hfe; rw [hk'] at hfe; exact absurd hfe (by decide)

end Noperthedron.PentagonalHexecontahedron.Cap
