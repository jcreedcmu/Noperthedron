module

public import Cayley.Soundness.KDomPoly
public import Cayley.Soundness.KGapSound

@[expose] public section

/-!
# Soundness of the kernel domain leaves
-/

namespace Cayley.Pack

set_option exponentiation.threshold 1024

open Cayley.K Matrix

/-! ## The chart test -/

/-- The chart-test expression. -/
def chartPE (b : KBox) (k : ℕ) : PE := chartGen PE.add PE.sub PE.mul PE.c PE.x b k

theorem chartPE_int (b : KBox) (k : ℕ) :
    (chartPE b k).ev pXv = chartGen Int.add Int.sub Int.mul (fun z => z) (fun i => pX i.val) b k :=
  chartGen_map PE.add PE.sub PE.mul PE.c PE.x Int.add Int.sub Int.mul (fun z => z)
    (fun i => pX i.val) (PE.ev pXv) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => by simp [PE.ev]) (fun _ => rfl) b k

theorem chartPE_real (b : KBox) (k : ℕ) (t : Fin 5 → ℝ) :
    (chartPE b k).ev t = chartGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b k :=
  chartGen_map PE.add PE.sub PE.mul PE.c PE.x (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t
    (PE.ev t) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) b k

theorem chartPE_nrm (b : KBox) (k : ℕ) :
    (chartPE b k).nrm = chartGen Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1) b k :=
  chartGen_map PE.add PE.sub PE.mul PE.c PE.x Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1)
    PE.nrm (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) b k

theorem chartPE_fits (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) (k : ℕ) (hk : k < 5) :
    L3.Fits (chartPE b k) := by
  intro i
  have h := congrFun (chartGen_map PE.add PE.sub PE.mul PE.c PE.x dAdd dAdd dMul dC dX
    (fun e i => e.deg i) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) b k) i
  rw [chartGen_deg] at h
  have h2 := chart_deg_closed _ hj _ hf _ hk i
  rw [chartPE, h]
  have : dBound 0 i ≤ 2 := by simp only [dBound]; split_ifs <;> simp
  show _ < 3
  omega

theorem pChartOK_sound (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) {k : ℕ} (hk : k < 5)
    (h : pChartOK b k = true) {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) :
    trace ((chartB b.chart)ᵀ * Qm b.chart (rOf (kblow b.chart) b.face (kpt b t))) <
      trace ((chartB k)ᵀ * Qm b.chart (rOf (kblow b.chart) b.face (kpt b t))) := by
  unfold pChartOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hn, hp⟩ := h
  have hn' : (chartPE b k).nrm < O := by
    rw [chartPE_nrm, O_eq]; unfold chartNrmOK at hn; rwa [Nat.blt_eq] at hn
  have hp' := of_decide_eq_true hp
  rw [← chartPE_int] at hp'
  have hl : ((pLower ((chartPE b k).ev pXv) : ℤ) : ℝ) ≤ (chartPE b k).ev t :=
    pLower_le (chartPE_fits b hj hf k hk) hn' ht
  rw [chartPE_real, chartR_eq b hj k hk t] at hl
  have h0 : (0 : ℝ) < ((pLower ((chartPE b k).ev pXv) : ℤ) : ℝ) := by exact_mod_cast hp'
  set r := rOf (kblow b.chart) b.face (kpt b t)
  have hκ1 := kapJ_ge b.chart
  have hκ2 := kapJ_ge k
  have hB : 0 < betaSc b := by unfold betaSc; split_ifs <;> positivity
  have hD := cayleyDenom_pos (r 0) (r 1) (r 2)
  have hK : 0 < kapJ b.chart ^ 2 * kapJ k * (betaSc b * cayleyDenom (r 0) (r 1) (r 2)) := by positivity
  have := lt_of_lt_of_le h0 hl
  have := (pos_iff_pos_of_mul_pos this).1 hK
  linarith

/-! ## The orbit test -/

open Cayley

theorem Hmat_mem_SO3 (u v : ℝ) : Hmat u v ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hZ : ZR ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    rw [mem_SO3_iff']
    exact ⟨by ext a b; fin_cases a <;> fin_cases b <;> simp [ZR, Matrix.mul_apply, Fin.sum_univ_three],
      by simp [ZR, Matrix.det_fin_three]⟩
  have hS := outerRot_mem_SO3 u v
  have hT : (outerRot u v)ᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    rw [mem_SO3_iff'] at hS ⊢
    exact ⟨by rw [Matrix.transpose_transpose, SO3_transpose_mul (outerRot_mem_SO3 u v)],
      by rw [Matrix.det_transpose]; exact hS.2⟩
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hT hZ) hS

theorem entry_le_one {Z : Matrix (Fin 3) (Fin 3) ℝ} (hZ : Z ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (a c : Fin 3) : |Z a c| ≤ 1 := by
  have h := congrFun (congrFun (SO3_mul_transpose hZ) a) a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h
  rw [abs_le]
  fin_cases c <;> simp <;> constructor <;> nlinarith [sq_nonneg (Z a 0), sq_nonneg (Z a 1),
    sq_nonneg (Z a 2)]

theorem trace_mul_approx {Z : Matrix (Fin 3) (Fin 3) ℝ} (hZ : Z ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {G G' : Matrix (Fin 3) (Fin 3) ℝ} {ε : ℝ} (hG : ∀ a c, |G a c - G' a c| ≤ ε) :
    |Matrix.trace (Z * G) - Matrix.trace (Z * G')| ≤ 9 * ε := by
  have hterm : ∀ a c, |Z a c * G c a - Z a c * G' c a| ≤ ε := by
    intro a c
    rw [← mul_sub, abs_mul]
    calc |Z a c| * |G c a - G' c a| ≤ 1 * ε :=
          mul_le_mul (entry_le_one hZ a c) (hG c a) (abs_nonneg _) (by norm_num)
      _ = ε := one_mul ε
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  have := hterm 0 0; have := hterm 0 1; have := hterm 0 2
  have := hterm 1 0; have := hterm 1 1; have := hterm 1 2
  have := hterm 2 0; have := hterm 2 1; have := hterm 2 2
  rw [abs_le] at *
  constructor <;> linarith


/-- The orbit-test expressions. -/
def orbPE (b : KBox) (e g a : ℕ) : PE × PE := orbGen PE.add PE.sub PE.mul PE.c PE.x b e g a

theorem orbPE_ev {R : Type} [CommRing R] (v : Fin 5 → R) (b : KBox) (e g a : ℕ) :
    ((orbPE b e g a).1.ev v = (orbGen (· + ·) (· - ·) (· * ·) (fun z => (z : R)) v b e g a).1) ∧
      ((orbPE b e g a).2.ev v = (orbGen (· + ·) (· - ·) (· * ·) (fun z => (z : R)) v b e g a).2) :=
  orbGen_map PE.add PE.sub PE.mul PE.c PE.x (· + ·) (· - ·) (· * ·) (fun z => (z : R)) v (PE.ev v)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) b e g a

theorem orbPE_nrm (b : KBox) (e g a : ℕ) :
    (orbPE b e g a).1.nrm = (orbGen Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1) b e g a).1 ∧
      (orbPE b e g a).2.nrm = (orbGen Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1) b e g a).2 :=
  orbGen_map PE.add PE.sub PE.mul PE.c PE.x Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1) PE.nrm
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) b e g a

theorem orbPE_deg (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) (e : ℕ) (he : e < 2) (g a : ℕ)
    (ha : a = 0 ∨ a = 4) (i : Fin 5) :
    (orbPE b e g a).1.deg i ≤ dBound e i ∧ (orbPE b e g a).2.deg i ≤ dBound e i := by
  obtain ⟨h1, h2⟩ := orbGen_map PE.add PE.sub PE.mul PE.c PE.x dAdd dAdd dMul dC dX
    (fun e i => e.deg i) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) b e g a
  have h1i := congrFun h1 i
  have h2i := congrFun h2 i
  rw [orbGen_deg, orbGen_deg_g] at h1i h2i
  obtain ⟨c1, c2, c3, c4⟩ := orb_deg_closed _ hj _ hf _ he i
  simp only [orbPE]
  rw [h1i, h2i]
  rcases ha with rfl | rfl
  · exact ⟨c1, c2⟩
  · exact ⟨c3, c4⟩

/-- The orbit scale. -/
noncomputable def orbK (b : KBox) (e : ℕ) (t : Fin 5 → ℝ) : ℝ :=
  let r := rOf (kblow b.chart) b.face (kpt b t)
  kapJ 4 * kapJ b.chart * 2 ^ 80 * (betaSc b * cayleyDenom (r 0) (r 1) (r 2)) *
    (if e = 0 then 1 else ((2 : ℝ) ^ b.K) ^ 4 * cayleyDenom (kpt b t 1) (-kpt b t 0) 0 ^ 2)

/-- The orbit element `Y`. -/
noncomputable def orbY (b : KBox) (e : ℕ) (t : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  if e = 0 then 1 else Hmat (kpt b t 0) (kpt b t 1)

theorem L5_fits_of {e : PE} (h : ∀ i, e.deg i ≤ dBound 1 i) : L5.Fits e := by
  intro i; have := h i; fin_cases i <;> simp [dBound, L5] at this ⊢ <;> omega

theorem L3_fits_of {e : PE} (h : ∀ i, e.deg i ≤ dBound 0 i) : L3.Fits e := by
  intro i; have := h i; fin_cases i <;> simp [dBound, L3] at this ⊢ <;> omega

/-- A passing orbit test bounds both score differences from below. -/
theorem orbit_bounds (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) {e g a : ℕ} (he : e < 2)
    (hg : g < 15) (ha : a = 0 ∨ a = 4) (h : pOrbitOK b e g a = true) {t : Fin 5 → ℝ}
    (ht : ∀ i, |t i| ≤ 1) :
    let r := rOf (kblow b.chart) b.face (kpt b t)
    let Q := Qm b.chart r
    let F := trace ((chartB a)ᵀ * (orbY b e t * Q) * gHat g) - (if a = 4 then 1 / 8 else 0)
    ((orbErr b e : ℤ) : ℝ) < orbK b e t * (F - trace Q) ∧
      ((orbErr b e : ℤ) : ℝ) < orbK b e t * (F - (trace (tauRᵀ * Q) - 1 / 8)) := by
  intro r Q F
  unfold pOrbitOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hn, hrest⟩ := h
  unfold orbNrmOK at hn
  simp only [Bool.and_eq_true, Nat.blt_eq] at hn
  obtain ⟨n1, n2⟩ := orbPE_nrm b e g a
  have hb1 : (orbPE b e g a).1.nrm < O := by rw [n1, O_eq]; exact hn.1
  have hb2 : (orbPE b e g a).2.nrm < O := by rw [n2, O_eq]; exact hn.2
  obtain ⟨r1, r2⟩ := orbPE_ev t b e g a
  have hdeg := orbPE_deg b hj hf e he g a ha
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · simp only [↓reduceIte, Bool.and_eq_true] at hrest
    obtain ⟨p1, p2⟩ := hrest
    obtain ⟨i1, i2⟩ := orbGen_map PE.add PE.sub PE.mul PE.c PE.x Int.add Int.sub Int.mul (fun z => z)
      (fun i => pX i.val) (PE.ev pXv) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => by simp [PE.ev]) (fun _ => rfl) b 0 g a
    have l1 := pLower_le (L3_fits_of fun i => (hdeg i).1) hb1 ht
    have l2 := pLower_le (L3_fits_of fun i => (hdeg i).2) hb2 ht
    have q1 := of_decide_eq_true p1
    have q2 := of_decide_eq_true p2
    change _ < pLower (orbGen Int.add Int.sub Int.mul (fun z => z) (fun i => pX i.val) b 0 g a).1 at q1
    change _ < pLower (orbGen Int.add Int.sub Int.mul (fun z => z) (fun i => pX i.val) b 0 g a).2 at q2
    rw [← i1] at q1
    rw [← i2] at q2
    obtain ⟨e1, e2⟩ := orbR0 b hj g hg a ha t
    have c1 : ((orbErr b 0 : ℤ) : ℝ) < ((pLower ((orbPE b 0 g a).1.ev pXv) : ℤ) : ℝ) := by exact_mod_cast q1
    have c2 : ((orbErr b 0 : ℤ) : ℝ) < ((pLower ((orbPE b 0 g a).2.ev pXv) : ℤ) : ℝ) := by exact_mod_cast q2
    rw [r1] at l1; rw [r2] at l2
    simp only [F, orbK, orbY, ↓reduceIte, mul_one, Matrix.one_mul]
    exact ⟨lt_of_lt_of_le c1 (l1.trans_eq e1), lt_of_lt_of_le c2 (l2.trans_eq e2)⟩
  · simp only [one_ne_zero, ↓reduceIte, Bool.and_eq_true] at hrest
    obtain ⟨p1, p2⟩ := hrest
    obtain ⟨i1, i2⟩ := orbGen_map PE.add PE.sub PE.mul PE.c PE.x Int.add Int.sub Int.mul (fun z => z)
      qXv (PE.ev qXv) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => by simp [PE.ev]) (fun _ => rfl) b 1 g a
    have l1 := qLower_le (L5_fits_of fun i => (hdeg i).1) hb1 ht
    have l2 := qLower_le (L5_fits_of fun i => (hdeg i).2) hb2 ht
    have q1 := of_decide_eq_true p1
    have q2 := of_decide_eq_true p2
    change _ < qLower (orbGen Int.add Int.sub Int.mul (fun z => z) qXv b 1 g a).1 at q1
    change _ < qLower (orbGen Int.add Int.sub Int.mul (fun z => z) qXv b 1 g a).2 at q2
    rw [← i1] at q1
    rw [← i2] at q2
    obtain ⟨e1, e2⟩ := orbR1 b hj g hg a ha t
    have c1 : ((orbErr b 1 : ℤ) : ℝ) < ((qLower ((orbPE b 1 g a).1.ev qXv) : ℤ) : ℝ) := by exact_mod_cast q1
    have c2 : ((orbErr b 1 : ℤ) : ℝ) < ((qLower ((orbPE b 1 g a).2.ev qXv) : ℤ) : ℝ) := by exact_mod_cast q2
    rw [r1] at l1; rw [r2] at l2
    simp only [F, orbK, orbY, one_ne_zero, ↓reduceIte]
    refine ⟨lt_of_lt_of_le c1 (l1.trans_eq ?_), lt_of_lt_of_le c2 (l2.trans_eq ?_)⟩
    · rw [e1]; ring
    · rw [e2]; ring

/-- **Soundness of a kernel orbit leaf.** -/
theorem pOrbitOK_sound (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) {e g a : ℕ} (he : e < 2)
    (hg : g < 15) (ha : a = 0 ∨ a = 4) (h : pOrbitOK b e g a = true) {t : Fin 5 → ℝ}
    (ht : ∀ i, |t i| ≤ 1) (hpt : PtOK b.chart b.face (kpt b t)) :
    Fsc (Qm b.chart (rOf (kblow b.chart) b.face (kpt b t))) <
      Fsc (orbY b e t * Qm b.chart (rOf (kblow b.chart) b.face (kpt b t)) * gR g) := by
  obtain ⟨h0, h4⟩ := orbit_bounds b hj hf he hg ha h ht
  set r := rOf (kblow b.chart) b.face (kpt b t)
  set Q := Qm b.chart r
  set K := orbK b e t
  set ε : ℝ := 1 / 2 ^ 60
  have hε : 0 < ε := by positivity
  have hκ4 := kapJ_ge 4
  have hκj := kapJ_ge b.chart
  have hDr : 1 ≤ cayleyDenom (r 0) (r 1) (r 2) ∧ cayleyDenom (r 0) (r 1) (r 2) ≤ 13 := by
    have r0 := hpt.rb 0; have r1 := hpt.rb 1; have r2 := hpt.rb 2
    rw [abs_le] at r0 r1 r2
    simp only [cayleyDenom]
    constructor <;> nlinarith [sq_nonneg (r 0), sq_nonneg (r 1), sq_nonneg (r 2)]
  have hDo : 1 ≤ cayleyDenom (kpt b t 1) (-kpt b t 0) 0 ∧ cayleyDenom (kpt b t 1) (-kpt b t 0) 0 ≤ 2 := by
    simp only [cayleyDenom]
    constructor <;> nlinarith [hpt.disk, sq_nonneg (kpt b t 0), sq_nonneg (kpt b t 1)]
  have hB : 0 < betaSc b := by unfold betaSc; split_ifs <;> positivity
  have hK : 0 < K := by
    simp only [K, orbK]
    have : 0 < (if e = 0 then (1 : ℝ) else ((2 : ℝ) ^ b.K) ^ 4 *
        cayleyDenom (kpt b t 1) (-kpt b t 0) 0 ^ 2) := by
      split_ifs
      · norm_num
      · have := hDo.1; positivity
    have := hDr.1
    positivity
  -- the error allowance covers the symmetry-table error
  have hErr : 9 * ε * K ≤ ((orbErr b e : ℤ) : ℝ) := by
    have hp20 : ((p2 20 : ℤ) : ℝ) = 2 ^ 20 := p2_cast 20
    have hsc := numSc_real b
    simp only [K, orbK, orbErr, ε]
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · simp only [↓reduceIte, mul_one]
      push_cast [hp20, hsc]
      have hk4 : ((kappaTau : ℤ) : ℝ) = kapJ 4 := rfl
      have hkj : ((chartKI b.chart : ℤ) : ℝ) = kapJ b.chart := rfl
      rw [hk4, hkj]
      have : kapJ 4 * kapJ b.chart * betaSc b * cayleyDenom (r 0) (r 1) (r 2) ≤
          kapJ 4 * kapJ b.chart * betaSc b * 13 :=
        mul_le_mul_of_nonneg_left hDr.2 (by positivity)
      have hp : (0 : ℝ) < kapJ 4 * kapJ b.chart * betaSc b := by positivity
      nlinarith
    · simp only [one_ne_zero, ↓reduceIte]
      push_cast [hp20, hsc, p2_cast]
      have hk4 : ((kappaTau : ℤ) : ℝ) = kapJ 4 := rfl
      have hkj : ((chartKI b.chart : ℤ) : ℝ) = kapJ b.chart := rfl
      rw [hk4, hkj]
      have hDo2 : cayleyDenom (kpt b t 1) (-kpt b t 0) 0 ^ 2 ≤ 4 := by nlinarith [hDo.1, hDo.2]
      have h52 : cayleyDenom (r 0) (r 1) (r 2) * cayleyDenom (kpt b t 1) (-kpt b t 0) 0 ^ 2 ≤ 52 := by
        nlinarith [hDr.1, hDr.2, sq_nonneg (cayleyDenom (kpt b t 1) (-kpt b t 0) 0)]
      have hU : (0 : ℝ) < ((2 : ℝ) ^ b.K) ^ 4 := by positivity
      have hp : (0 : ℝ) < kapJ 4 * kapJ b.chart * betaSc b * ((2 : ℝ) ^ b.K) ^ 4 := by positivity
      nlinarith
  -- the true score of the orbit element is within `9ε` of the checked one
  set Y := orbY b e t
  have hYQ : (chartB a)ᵀ * (Y * Q) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have hBt : (chartB a)ᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
      have hB' := chartB_mem_SO3 a
      rw [mem_SO3_iff'] at hB' ⊢
      exact ⟨by rw [Matrix.transpose_transpose, SO3_transpose_mul (chartB_mem_SO3 a)],
        by rw [Matrix.det_transpose]; exact hB'.2⟩
    have hY : Y ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
      simp only [Y, orbY]; split_ifs
      · exact Submonoid.one_mem _
      · exact Hmat_mem_SO3 _ _
    exact Submonoid.mul_mem _ hBt (Submonoid.mul_mem _ hY
      (Submonoid.mul_mem _ (chartB_mem_SO3 _) (cayV_mem_SO3 _)))
  have happ := trace_mul_approx hYQ (G := gR g) (G' := gHat g)
    (fun a c => by have := group_approx g hg a c; rwa [D_errε] at this)
  set Ft := trace ((chartB a)ᵀ * (Y * Q) * gR g) - (if a = 4 then 1 / 8 else 0)
  set F' := trace ((chartB a)ᵀ * (Y * Q) * gHat g) - (if a = 4 then 1 / 8 else 0)
  have hFF : F' - 9 * ε ≤ Ft := by
    simp only [Ft, F']; linarith [(abs_le.1 happ).1]
  have hF0 : trace Q < Ft := by
    have : K * (9 * ε) < K * (F' - trace Q) :=
      calc K * (9 * ε) = 9 * ε * K := by ring
        _ ≤ _ := hErr
        _ < _ := h0
    have := lt_of_mul_lt_mul_left this hK.le
    linarith
  have hF4 : trace (tauRᵀ * Q) - 1 / 8 < Ft := by
    have : K * (9 * ε) < K * (F' - (trace (tauRᵀ * Q) - 1 / 8)) :=
      calc K * (9 * ε) = 9 * ε * K := by ring
        _ ≤ _ := hErr
        _ < _ := h4
    have h' : 9 * ε < F' - (trace (tauRᵀ * Q) - 1 / 8) := lt_of_mul_lt_mul_left this hK.le
    calc trace (tauRᵀ * Q) - 1 / 8 < F' - 9 * ε := by linarith
      _ ≤ Ft := hFF
  have hFsc : Ft ≤ Fsc (Y * Q * gR g) := by
    simp only [Ft, Fsc]
    rcases ha with rfl | rfl
    · simp only [chartB_zero_eq, transpose_one, Matrix.one_mul, show ((0 : ℕ) = 4) = False by decide,
        ↓reduceIte, sub_zero, Matrix.mul_assoc]
      exact le_max_left _ _
    · simp only [ite_true, Matrix.mul_assoc]
      exact le_max_right _ _
  exact lt_of_lt_of_le (max_lt hF0 hF4) hFsc

/-! ## The domain leaf -/

theorem kpt_ge (b : KBox) (t : Fin 5 → ℝ) (ht : ∀ i, |t i| ≤ 1) (i : Fin 5) (hh : 0 ≤ b.h.getD i 0) :
    ((b.c.getD i 0 - b.h.getD i 0 : ℤ) : ℝ) / 2 ^ b.K ≤ kpt b t i ∧
      kpt b t i ≤ ((b.c.getD i 0 + b.h.getD i 0 : ℤ) : ℝ) / 2 ^ b.K := by
  have ht' := abs_le.1 (ht i)
  have hh' : (0 : ℝ) ≤ (b.h.getD i 0 : ℝ) := by exact_mod_cast hh
  simp only [kpt]
  constructor <;> (apply div_le_div_of_nonneg_right _ (by positivity); push_cast; nlinarith)

/-- **Soundness of a kernel domain leaf.** -/
theorem pDomOK_sound (b : KBox) (hj : b.chart < 5) (hf : b.face < 6)
    (hh : ∀ i : Fin 5, 0 ≤ b.h.getD i 0) {code : ℕ} (h : pDomOK b code = true) {t : Fin 5 → ℝ}
    (ht : ∀ i, |t i| ≤ 1) (hpt : PtOK b.chart b.face (kpt b t)) :
    ¬ Reduced (kpt b t 0) (kpt b t 1) b.chart (rOf (kblow b.chart) b.face (kpt b t)) := by
  intro hR
  unfold pDomOK at h
  have hU : (0 : ℝ) < 2 ^ b.K := by positivity
  obtain ⟨u0, u1⟩ := kpt_ge b t ht 0 (hh 0)
  obtain ⟨v0, v1⟩ := kpt_ge b t ht 1 (hh 1)
  simp only [Fin.val_zero, Fin.val_one, Fin.isValue] at u0 u1 v0 v1
  split_ifs at h with c0 c1 c7 c67
  · -- disk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hu, hv⟩, hd⟩ := h
    have hd' : ((2 : ℝ) ^ b.K) ^ 2 < ((b.c.getD 0 0 - b.h.getD 0 0 : ℤ) : ℝ) ^ 2 +
        ((b.c.getD 1 0 - b.h.getD 1 0 : ℤ) : ℝ) ^ 2 := by
      have : ((p2 b.K * p2 b.K : ℤ) : ℝ) < (((b.c.getD 0 0 - b.h.getD 0 0) * (b.c.getD 0 0 - b.h.getD 0 0) +
          (b.c.getD 1 0 - b.h.getD 1 0) * (b.c.getD 1 0 - b.h.getD 1 0) : ℤ) : ℝ) := by exact_mod_cast hd
      push_cast [p2_cast] at this ⊢; nlinarith [this]
    have hu' : (0 : ℝ) ≤ ((b.c.getD 0 0 - b.h.getD 0 0 : ℤ) : ℝ) := by exact_mod_cast hu
    have hv' : (0 : ℝ) ≤ ((b.c.getD 1 0 - b.h.getD 1 0 : ℤ) : ℝ) := by exact_mod_cast hv
    have e0 : ((b.c.getD 0 0 - b.h.getD 0 0 : ℤ) : ℝ) ≤ 2 ^ b.K * kpt b t 0 := by
      rw [div_le_iff₀ hU] at u0; linarith
    have e1 : ((b.c.getD 1 0 - b.h.getD 1 0 : ℤ) : ℝ) ≤ 2 ^ b.K * kpt b t 1 := by
      rw [div_le_iff₀ hU] at v0; linarith
    have hdisk := hR.disk
    have : ((2 : ℝ) ^ b.K) ^ 2 < ((2 : ℝ) ^ b.K) ^ 2 * (kpt b t 0 ^ 2 + kpt b t 1 ^ 2) := by
      nlinarith [mul_le_mul e0 e0 hu' (by linarith), mul_le_mul e1 e1 hv' (by linarith)]
    nlinarith
  · -- wedge
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hu, hw⟩ := h
    have hw' : 57 * ((b.c.getD 0 0 + b.h.getD 0 0 : ℤ) : ℝ) < 128 * ((b.c.getD 1 0 - b.h.getD 1 0 : ℤ) : ℝ) := by
      exact_mod_cast hw
    have e0 : 2 ^ b.K * kpt b t 0 ≤ ((b.c.getD 0 0 + b.h.getD 0 0 : ℤ) : ℝ) := by
      rw [le_div_iff₀ hU] at u1; linarith
    have e1 : ((b.c.getD 1 0 - b.h.getD 1 0 : ℤ) : ℝ) ≤ 2 ^ b.K * kpt b t 1 := by
      rw [div_le_iff₀ hU] at v0; linarith
    have hwedge := hR.wedge
    have : 2 ^ b.K * (57 * kpt b t 0) < 2 ^ b.K * (128 * kpt b t 1) := by linarith
    have := lt_of_mul_lt_mul_left this hU.le
    linarith
  · -- chart
    have hk : code - 2 < 5 := by omega
    have := pChartOK_sound b hj hf hk h ht
    linarith [hR.chart (code - 2) hk]
  · -- orbit
    set i := code - 7
    have he : i / 30 < 2 := by omega
    have hg : i / 2 % 15 < 15 := Nat.mod_lt _ (by norm_num)
    have ha : (if i % 2 = 0 then 0 else 4) = 0 ∨ (if i % 2 = 0 then 0 else 4) = 4 := by
      split_ifs <;> simp
    have := pOrbitOK_sound b hj hf he hg ha h ht hpt
    have hY : orbY b (i / 30) t =
        if (decide (i / 30 ≠ 0)) then Hmat (kpt b t 0) (kpt b t 1) else 1 := by
      simp only [orbY]; by_cases hz : i / 30 = 0 <;> simp [hz]
    rw [hY] at this
    have := hR.orbit (decide (i / 30 ≠ 0)) (i / 2 % 15)
    linarith

end Cayley.Pack

end
