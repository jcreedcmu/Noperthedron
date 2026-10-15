module

public import Cayley.Soundness.KGapPoly
public import Cayley.Soundness.Reduction

@[expose] public section

/-!
# The domain-leaf polynomials

`numGen`, `chartGen` and `orbGen` are generic in the arithmetic; maps that commute with the
operations commute with them.
-/

namespace Cayley.Pack

open Cayley.K

section map

variable {R S : Type} (addR subR mulR : R → R → R) (cR : ℤ → R) (xR : Fin 5 → R)
  (addS subS mulS : S → S → S) (cS : ℤ → S) (xS : Fin 5 → S) (f : R → S)
  (hadd : ∀ a b, f (addR a b) = addS (f a) (f b)) (hsub : ∀ a b, f (subR a b) = subS (f a) (f b))
  (hmul : ∀ a b, f (mulR a b) = mulS (f a) (f b)) (hc : ∀ z, f (cR z) = cS z)
  (hx : ∀ i, f (xR i) = xS i)
include hadd hsub hmul hc hx

/-- `f` applied to every entry. -/
def _root_.Cayley.K.NM.map {R S : Type} (f : R → S) (N : NM R) : NM S :=
  ⟨f N.n00, f N.n01, f N.n02, f N.n10, f N.n11, f N.n12, f N.n20, f N.n21, f N.n22, f N.d⟩

theorem numGen_map (b : KBox) :
    (numGen addR subR mulR cR xR b).map f = numGen addS subS mulS cS xS b := by
  have hf1 := fun face a b c => (gFace_map f face a b c).1
  have hf2 := fun face a b c => (gFace_map f face a b c).2.1
  have hf3 := fun face a b c => (gFace_map f face a b c).2.2
  simp only [numGen]
  split_ifs <;> simp only [NM.map, hf1, hf2, hf3, hadd, hsub, hmul, hc, hx]

omit hx hsub in
theorem trGen_map (X : I9) (N : NM R) :
    f (trGen addR mulR cR X N) = trGen addS mulS cS X (N.map f) := by
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := X
  simp only [trGen, NM.map, hadd, hmul, hc]

theorem chartGen_map (b : KBox) (k : ℕ) :
    f (chartGen addR subR mulR cR xR b k) = chartGen addS subS mulS cS xS b k := by
  simp only [chartGen, hsub, hmul, hc,
    trGen_map addR mulR cR addS mulS cS f hadd hmul hc,
    numGen_map addR subR mulR cR xR addS subS mulS cS xS f hadd hsub hmul hc hx]

omit hx hsub in
theorem m3_map (M : I9) (N : NM R) :
    (m3 addR mulR cR M N).map f = m3 addS mulS cS M (N.map f) := by
  obtain ⟨m00, m01, m02, m10, m11, m12, m20, m21, m22⟩ := M
  simp only [m3, NM.map, hadd, hmul, hc]

omit hadd hsub hmul hc hx in
theorem m3t_map (N : NM R) : (m3t N).map f = m3t (N.map f) := rfl

omit hx hsub hc in
theorem frob_map (H W : NM R) : f (frob addR mulR H W) = frob addS mulS (H.map f) (W.map f) := by
  simp only [frob, NM.map, hadd, hmul]

omit hx in
theorem hGen_map (u v U : R) :
    (hGen addR subR mulR cR u v U).map f = hGen addS subS mulS cS (f u) (f v) (f U) := by
  simp only [hGen, NM.map, hadd, hsub, hmul, hc]

theorem orbGen_map (b : KBox) (e g a : ℕ) :
    f (orbGen addR subR mulR cR xR b e g a).1 = (orbGen addS subS mulS cS xS b e g a).1 ∧
      f (orbGen addR subR mulR cR xR b e g a).2 = (orbGen addS subS mulS cS xS b e g a).2 := by
  have ht := trGen_map addR mulR cR addS mulS cS f hadd hmul hc
  have hn := numGen_map addR subR mulR cR xR addS subS mulS cS xS f hadd hsub hmul hc hx b
  have hd := congrArg NM.d hn
  simp only [NM.map] at hd
  have hm := m3_map (addR := addR) (mulR := mulR) (cR := cR) (addS := addS) (mulS := mulS) (cS := cS)
    (f := f) (hadd := hadd) (hmul := hmul) (hc := hc)
  have hf := frob_map (addR := addR) (mulR := mulR) (addS := addS) (mulS := mulS) (f := f)
    (hadd := hadd) (hmul := hmul)
  have hh := hGen_map (addR := addR) (subR := subR) (mulR := mulR) (cR := cR) (addS := addS)
    (subS := subS) (mulS := mulS) (cS := cS) (f := f) (hadd := hadd) (hsub := hsub) (hmul := hmul) (hc := hc)
  simp only [orbGen]
  split_ifs <;> simp only [ht, hn, hd, hadd, hsub, hmul, hc, hx, and_self, hf, hh, hm, m3t_map]

end map

/-! ## Degrees -/

/-- The degree algebra. -/
def dAdd (a c : Fin 5 → ℕ) : Fin 5 → ℕ := fun i => max (a i) (c i)
def dMul (a c : Fin 5 → ℕ) : Fin 5 → ℕ := fun i => a i + c i
abbrev dC : ℤ → Fin 5 → ℕ := fun _ _ => 0
def dX (j : Fin 5) : Fin 5 → ℕ := fun i => if j = i then 1 else 0

/-- The degree instance only sees the chart and the face. -/
theorem numGen_deg (b : KBox) :
    numGen dAdd dAdd dMul dC dX b = numGen dAdd dAdd dMul dC dX ⟨b.chart, b.face, 0, [], []⟩ := by
  simp only [numGen]

theorem chartGen_deg (b : KBox) (k : ℕ) :
    chartGen dAdd dAdd dMul dC dX b k = chartGen dAdd dAdd dMul dC dX ⟨b.chart, b.face, 0, [], []⟩ k := by
  simp only [chartGen, numGen_deg b]

theorem orbGen_deg (b : KBox) (e g a : ℕ) :
    orbGen dAdd dAdd dMul dC dX b e g a = orbGen dAdd dAdd dMul dC dX ⟨b.chart, b.face, 0, [], []⟩ e g a := by
  simp only [orbGen, numGen_deg b]

theorem trGen_dC (X X' : I9) (N : NM (Fin 5 → ℕ)) : trGen dAdd dMul dC X N = trGen dAdd dMul dC X' N := by
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := X
  obtain ⟨y00, y01, y02, y10, y11, y12, y20, y21, y22⟩ := X'
  rfl

theorem m3_dC (X X' : I9) (N : NM (Fin 5 → ℕ)) : m3 dAdd dMul dC X N = m3 dAdd dMul dC X' N := by
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := X
  obtain ⟨y00, y01, y02, y10, y11, y12, y20, y21, y22⟩ := X'
  rfl

theorem orbGen_deg_g (b : KBox) (e g a : ℕ) :
    orbGen dAdd dAdd dMul dC dX b e g a = orbGen dAdd dAdd dMul dC dX b e 0 a := by
  simp only [orbGen]
  rw [trGen_dC (mtm (chartMI b.chart) (orbC g a)) (mtm (chartMI b.chart) (orbC 0 a)),
    m3_dC (orbC g a) (orbC 0 a)]

/-- Degree bounds: `t₀, t₁` absent (chart, orbit `e = 0`) or of degree `≤ 4` (orbit `e = 1`). -/
def dBound (e : ℕ) (i : Fin 5) : ℕ := if i.val < 2 then (if e = 0 then 0 else 4) else 2

theorem chart_deg_closed : ∀ chart < 5, ∀ face < 6, ∀ k < 5, ∀ i : Fin 5,
    chartGen dAdd dAdd dMul dC dX ⟨chart, face, 0, [], []⟩ k i ≤ dBound 0 i := by
  decide +kernel

theorem orb_deg_closed : ∀ chart < 5, ∀ face < 6, ∀ e < 2, ∀ i : Fin 5,
    (orbGen dAdd dAdd dMul dC dX ⟨chart, face, 0, [], []⟩ e 0 0).1 i ≤ dBound e i ∧
    (orbGen dAdd dAdd dMul dC dX ⟨chart, face, 0, [], []⟩ e 0 0).2 i ≤ dBound e i ∧
    (orbGen dAdd dAdd dMul dC dX ⟨chart, face, 0, [], []⟩ e 0 4).1 i ≤ dBound e i ∧
    (orbGen dAdd dAdd dMul dC dX ⟨chart, face, 0, [], []⟩ e 0 4).2 i ≤ dBound e i := by
  decide +kernel

/-! ## The real instance -/

open Matrix

/-- The numerator at a real point. -/
noncomputable def numR (b : KBox) (t : Fin 5 → ℝ) : NM ℝ :=
  numGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b

/-- The matrix of an `NM`. -/
def nmat {R : Type} (N : NM R) : Matrix (Fin 3) (Fin 3) R :=
  !![N.n00, N.n01, N.n02; N.n10, N.n11, N.n12; N.n20, N.n21, N.n22]

theorem numSc_real (b : KBox) : ((numSc b : ℤ) : ℝ) = betaSc b := by
  unfold numSc betaSc; split_ifs <;> push_cast [p2_cast] <;> ring

theorem numR_eq (b : KBox) (t : Fin 5 → ℝ) :
    let r := rOf (kblow b.chart) b.face (kpt b t)
    nmat (numR b t) = betaSc b • cayleyNumeratorMatrix (r 0) (r 1) (r 2) ∧
      (numR b t).d = betaSc b * cayleyDenom (r 0) (r 1) (r 2) := by
  intro r
  have hF := gFace_real b.face (2 ^ b.K) (kpt b t 2) (kpt b t 3)
  simp only [numR, numGen, r, p2_cast, kptm2, kptm3, kptm4]
  by_cases hbl : b.chart = 0 ∨ b.chart = 4
  · have hk : kblow b.chart = true := by simp [kblow]; exact hbl
    simp only [hbl, ↓reduceIte, hF.1, hF.2.1, hF.2.2, betaSc, rOf, hk]
    generalize faceR b.face (kpt b t 2) (kpt b t 3) = fv
    generalize kpt b t 4 = ρ
    generalize (2 : ℝ) ^ b.K = U
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nmat, cayleyNumeratorMatrix] <;> ring
    · simp [cayleyDenom]; ring
  · have hk : kblow b.chart = false := by simp [kblow]; tauto
    simp only [hbl, ↓reduceIte, betaSc, rOf, hk, Bool.false_eq_true]
    generalize kpt b t 2 = x2
    generalize kpt b t 3 = x3
    generalize kpt b t 4 = x4
    generalize (2 : ℝ) ^ b.K = U
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nmat, cayleyNumeratorMatrix] <;> ring
    · simp [cayleyDenom]; ring

/-- The real matrix of an integer matrix. -/
noncomputable def imat (X : I9) : Matrix (Fin 3) (Fin 3) ℝ :=
  let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := X
  !![(m00 : ℝ), m01, m02; m10, m11, m12; m20, m21, m22]

theorem imat_chartMI (j : ℕ) : imat (chartMI j) = chartMR j := rfl

theorem trR (X : I9) (N : NM ℝ) :
    trGen (· + ·) (· * ·) (fun z => (z : ℝ)) X N = trace ((imat X)ᵀ * nmat N) := by
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := X
  simp [trGen, imat, nmat, trace, mul_apply, Fin.sum_univ_three]; ring

theorem imat_mtm (A B : I9) : imat (mtm A B) = (imat A)ᵀ * imat B := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ := A
  obtain ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩ := B
  ext i j; fin_cases i <;> fin_cases j <;> simp [imat, mtm, mul_apply, Fin.sum_univ_three]

/-- The chart-test polynomial at a real point. -/
theorem chartR_eq (b : KBox) (hj : b.chart < 5) (k : ℕ) (hk : k < 5) (t : Fin 5 → ℝ) :
    let r := rOf (kblow b.chart) b.face (kpt b t)
    chartGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b k =
      kapJ b.chart ^ 2 * kapJ k * (betaSc b * cayleyDenom (r 0) (r 1) (r 2)) *
        (trace ((chartB k)ᵀ * Qm b.chart r) - trace ((chartB b.chart)ᵀ * Qm b.chart r)) := by
  intro r
  obtain ⟨hN, -⟩ := numR_eq b t
  have hC : cayleyNumeratorMatrix (r 0) (r 1) (r 2) = cayleyDenom (r 0) (r 1) (r 2) • cayV r :=
    cayleyNumeratorMatrix_eq_denom_smul _ _ _
  have hBB : (chartB b.chart)ᵀ * chartB b.chart = 1 := chartB_transpose_mul_self _
  simp only [chartGen, trR, imat_mtm, imat_chartMI, chartMR_eq _ hj, chartMR_eq _ hk]
  change kapJ b.chart * trace (_ * nmat (numR b t)) - kapJ k * trace (_ * nmat (numR b t)) = _
  rw [hN, hC, smul_smul]
  simp only [transpose_mul, transpose_transpose, transpose_smul, smul_mul, mul_smul, trace_smul,
    smul_eq_mul, Qm, ← Matrix.mul_assoc, hBB, Matrix.one_mul]
  simp only [Matrix.mul_smul, trace_smul, smul_eq_mul]
  ring

/-! ## The orbit polynomials -/

theorem imat_mmI (A B : I9) : imat (mmI A B) = imat A * imat B := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ := A
  obtain ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩ := B
  ext i j; fin_cases i <;> fin_cases j <;> simp [imat, mmI, mul_apply, Fin.sum_univ_three]

/-- The tabulated symmetry `ĝ`. -/
noncomputable def gHat (g : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := (groupTab[g]!).toR

theorem cosTab_getD (g : ℕ) (hg : g < 15) : cosTab.getD g 0 = cosTab[g]! := by
  have : g < cosTab.size := by simp [cosTab]; omega
  simp [Array.getD, this, getElem!_pos]
theorem sinTab_getD (g : ℕ) (hg : g < 15) : sinTab.getD g 0 = sinTab[g]! := by
  have : g < sinTab.size := by simp [sinTab]; omega
  simp [Array.getD, this, getElem!_pos]

theorem tab_e80 : ∀ g < 15, (cosTab.getD g 0).e = 80 ∧ (sinTab.getD g 0).e = 80 := by decide +kernel

theorem imat_orbC (g a : ℕ) (hg : g < 15) :
    imat (orbC g a) = chartMR a * ((2 : ℝ) ^ 80 • (gHat g)ᵀ) := by
  rw [orbC, imat_mmI, imat_chartMI]
  congr 1
  have htab : groupTab[g]! = ⟨cosTab[g]!, -sinTab[g]!, 0, sinTab[g]!, cosTab[g]!, 0, 0, 0, 1⟩ := by
    simp [groupTab, getElem!_pos, hg]
  obtain ⟨hc, hs⟩ := tab_e80 g hg
  rw [cosTab_getD g hg] at hc ⊢
  rw [sinTab_getD g hg] at hs ⊢
  have hcD : D (cosTab[g]!) = ((cosTab[g]!).m : ℝ) / 2 ^ 80 := by rw [D, hc]
  have hsD : D (sinTab[g]!) = ((sinTab[g]!).m : ℝ) / 2 ^ 80 := by rw [D, hs]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [imat, gHat, htab, M3.toR, hcD, hsD, p2_cast] <;> field_simp

theorem kapJ_zero : kapJ 0 = 1 := by simp [kapJ, K.chartKI]
theorem chartB_zero_eq : chartB 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [chartB]

/-- The orbit polynomials for `e = 0` at a real point. -/
theorem orbR0 (b : KBox) (hj : b.chart < 5) (g : ℕ) (hg : g < 15) (a : ℕ) (ha : a = 0 ∨ a = 4)
    (t : Fin 5 → ℝ) :
    let r := rOf (kblow b.chart) b.face (kpt b t)
    let Q := Qm b.chart r
    let K := kapJ 4 * kapJ b.chart * 2 ^ 80 * (betaSc b * cayleyDenom (r 0) (r 1) (r 2))
    let F := trace ((chartB a)ᵀ * Q * gHat g) - (if a = 4 then 1 / 8 else 0)
    (orbGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b 0 g a).1 = K * (F - trace Q) ∧
      (orbGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b 0 g a).2 =
        K * (F - (trace (tauRᵀ * Q) - 1 / 8)) := by
  intro r Q K F
  obtain ⟨hN, hD⟩ := numR_eq b t
  simp only [numR] at hN hD
  change nmat _ = betaSc b • cayleyNumeratorMatrix (r 0) (r 1) (r 2) at hN
  change _ = betaSc b * cayleyDenom (r 0) (r 1) (r 2) at hD
  have hC : cayleyNumeratorMatrix (r 0) (r 1) (r 2) = cayleyDenom (r 0) (r 1) (r 2) • cayV r :=
    cayleyNumeratorMatrix_eq_denom_smul _ _ _
  have hM := chartMR_eq b.chart hj
  have h0 := chartMR_eq 0 (by norm_num)
  have h4 := chartMR_eq 4 (by norm_num)
  simp only [orbGen, ↓reduceIte, trR, imat_mtm, imat_chartMI, imat_orbC g a hg, hN, hD, hC, hM, h0, h4,
    kapJ_zero, chartB_zero_eq]
  have hk4 : ((kappaTau : ℤ) : ℝ) = kapJ 4 := rfl
  have hkj : ((chartKI b.chart : ℤ) : ℝ) = kapJ b.chart := rfl
  have hB4 : chartB 4 = tauR := rfl
  rcases ha with rfl | rfl
  · have ha' : chartMR 0 = 1 := by rw [h0, kapJ_zero, chartB_zero_eq, one_smul]
    simp only [ha', show ((0 : ℕ) = 4) = False by decide, ↓reduceIte, hB4]
    push_cast [p2_cast, hk4, hkj]
    simp only [Q, Qm, F, K, chartB_zero_eq, show ((0 : ℕ) = 4) = False by decide, ↓reduceIte]
    constructor <;>
    · simp only [trace, diag, mul_apply, transpose_apply, Matrix.smul_apply, smul_eq_mul,
        Fin.sum_univ_three, one_apply, Matrix.one_mul, Matrix.mul_one, one_smul]
      simp
      ring
  · rw [h4] at *
    simp only [hB4]
    push_cast [p2_cast, hk4, hkj]
    simp only [Q, Qm, F, K, hB4, ite_true]
    constructor <;>
    · simp only [trace, diag, mul_apply, transpose_apply, Matrix.smul_apply, smul_eq_mul,
        Fin.sum_univ_three, Matrix.mul_one, one_smul]
      simp
      ring

theorem kptm0 (b : KBox) (t : Fin 5 → ℝ) :
    ((b.c.getD 0 0 : ℤ) : ℝ) + ((b.h.getD 0 0 : ℤ) : ℝ) * t 0 = 2 ^ b.K * kpt b t 0 := by
  show _ = 2 ^ b.K * ((((b.c.getD 0 0 : ℤ) : ℝ) + ((b.h.getD 0 0 : ℤ) : ℝ) * t 0) / 2 ^ b.K)
  field_simp
theorem kptm1 (b : KBox) (t : Fin 5 → ℝ) :
    ((b.c.getD 1 0 : ℤ) : ℝ) + ((b.h.getD 1 0 : ℤ) : ℝ) * t 1 = 2 ^ b.K * kpt b t 1 := by
  show _ = 2 ^ b.K * ((((b.c.getD 1 0 : ℤ) : ℝ) + ((b.h.getD 1 0 : ℤ) : ℝ) * t 1) / 2 ^ b.K)
  field_simp

theorem nmat_m3 (M : I9) (N : NM ℝ) :
    nmat (m3 (· + ·) (· * ·) (fun z => (z : ℝ)) M N) = imat M * nmat N := by
  obtain ⟨m00, m01, m02, m10, m11, m12, m20, m21, m22⟩ := M
  ext i j; fin_cases i <;> fin_cases j <;> simp [m3, nmat, imat, mul_apply, Fin.sum_univ_three]

theorem nmat_m3t {R : Type} (N : NM R) : nmat (m3t N) = (nmat N)ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem frob_real (H W : NM ℝ) : frob (· + ·) (· * ·) H W = trace ((nmat H)ᵀ * nmat W) := by
  simp [frob, nmat, trace, mul_apply, Fin.sum_univ_three]; ring

theorem hGen_real (x : Fin 5 → ℝ) (U : ℝ) :
    nmat (hGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) (U * x 0) (U * x 1) U) =
      (U ^ 2 • NoR x)ᵀ * ZR * (U ^ 2 • NoR x) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hGen, nmat, NoR, cayleyNumeratorMatrix, ZR, mul_apply, Fin.sum_univ_three] <;> ring

/-- The orbit polynomials for `e = 1` at a real point. -/
theorem orbR1 (b : KBox) (hj : b.chart < 5) (g : ℕ) (hg : g < 15) (a : ℕ) (ha : a = 0 ∨ a = 4)
    (t : Fin 5 → ℝ) :
    let r := rOf (kblow b.chart) b.face (kpt b t)
    let Q := Qm b.chart r
    let Do := cayleyDenom (kpt b t 1) (-kpt b t 0) 0
    let K := kapJ 4 * kapJ b.chart * 2 ^ 80 * (betaSc b * cayleyDenom (r 0) (r 1) (r 2)) *
      ((2 : ℝ) ^ b.K) ^ 4 * Do ^ 2
    let F := trace ((chartB a)ᵀ * (Hmat (kpt b t 0) (kpt b t 1) * Q) * gHat g) -
      (if a = 4 then 1 / 8 else 0)
    (orbGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b 1 g a).1 = K * (F - trace Q) ∧
      (orbGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b 1 g a).2 =
        K * (F - (trace (tauRᵀ * Q) - 1 / 8)) := by
  intro r Q Do K F
  obtain ⟨hN, hD⟩ := numR_eq b t
  simp only [numR] at hN hD
  change nmat _ = betaSc b • cayleyNumeratorMatrix (r 0) (r 1) (r 2) at hN
  change _ = betaSc b * cayleyDenom (r 0) (r 1) (r 2) at hD
  have hC : cayleyNumeratorMatrix (r 0) (r 1) (r 2) = cayleyDenom (r 0) (r 1) (r 2) • cayV r :=
    cayleyNumeratorMatrix_eq_denom_smul _ _ _
  have hNo : NoR (kpt b t) = Do • outerRot (kpt b t 0) (kpt b t 1) :=
    cayleyNumeratorMatrix_eq_denom_smul _ _ _
  have hM := chartMR_eq b.chart hj
  have h0 := chartMR_eq 0 (by norm_num)
  have h4 := chartMR_eq 4 (by norm_num)
  have hk4 : ((kappaTau : ℤ) : ℝ) = kapJ 4 := rfl
  have hB4 : chartB 4 = tauR := rfl
  have hu := kptm0 b t
  have hv := kptm1 b t
  -- the pieces
  set U : ℝ := 2 ^ b.K with hU
  set Ro := outerRot (kpt b t 0) (kpt b t 1)
  set Hm := Hmat (kpt b t 0) (kpt b t 1)
  set βD := betaSc b * cayleyDenom (r 0) (r 1) (r 2)
  have hNm : nmat (numGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b) = βD • cayV r := by
    rw [hN, hC, smul_smul]
  have hHc : (U ^ 2 • NoR (kpt b t))ᵀ * ZR * (U ^ 2 • NoR (kpt b t)) = (U ^ 4 * Do ^ 2) • Hm := by
    rw [hNo]
    simp only [Hm, Hmat, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    congr 1; ring
  have hW : ∀ k : ℕ, k < 5 → chartMR k * ((2 : ℝ) ^ 80 • (gHat g)ᵀ) *
      (chartMR b.chart * nmat (numGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b))ᵀ =
      (kapJ k * kapJ b.chart * 2 ^ 80 * βD) • (chartB k * (gHat g)ᵀ * Qᵀ) := by
    intro k hk
    rw [chartMR_eq k hk, hM, hNm]
    simp only [Q, Qm, transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    congr 1; ring
  have htr : ∀ k : ℕ, k < 5 → trace (((chartMR b.chart)ᵀ * chartMR k)ᵀ *
      nmat (numGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b)) =
      kapJ k * kapJ b.chart * βD * trace ((chartB k)ᵀ * Q) := by
    intro k hk
    rw [chartMR_eq k hk, hM, hNm]
    simp only [Q, Qm, transpose_smul, transpose_mul, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul,
      trace_smul, smul_eq_mul, Matrix.mul_assoc]
    ring
  have hZ : ZRᵀ = ZR := by ext i j; fin_cases i <;> fin_cases j <;> simp [ZR]
  have key : ∀ (Ba : Matrix (Fin 3) (Fin 3) ℝ),
      trace (Hmᵀ * (Ba * (gHat g)ᵀ * Qᵀ)) = trace (Baᵀ * (Hm * Q) * gHat g) := by
    intro Ba
    rw [← trace_transpose]
    simp only [Hm, Hmat, Q, Qm, transpose_mul, transpose_transpose, hZ, Matrix.mul_assoc]
    rw [trace_mul_comm, Matrix.mul_assoc, trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hdo : (U * U + U * kpt b t 0 * (U * kpt b t 0) + U * kpt b t 1 * (U * kpt b t 1)) = U ^ 2 * Do := by
    simp only [Do, cayleyDenom]; ring
  -- the code as traces
  simp only [orbGen, one_ne_zero, ↓reduceIte, trR, frob_real, nmat_m3, nmat_m3t, imat_mtm,
    imat_chartMI, imat_orbC g a hg, p2_cast, hu, hv, hGen_real, hHc, hD, ← hU]
  rcases ha with rfl | rfl
  · rw [hW 0 (by norm_num), htr 0 (by norm_num), htr 4 (by norm_num)]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul, key, hdo]
    simp only [F, K, chartB_zero_eq, kapJ_zero, show ((0 : ℕ) = 4) = False by decide, ↓reduceIte,
      transpose_one, Matrix.one_mul]
    push_cast [hk4]
    have hkj : ((chartKI b.chart : ℤ) : ℝ) = kapJ b.chart := rfl
    simp only [p2_cast, hB4, hkj, U, βD, Hm]
    constructor <;> ring
  · rw [hW 4 (by norm_num), htr 0 (by norm_num), htr 4 (by norm_num)]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul, key, hdo]
    simp only [F, K, chartB_zero_eq, kapJ_zero, hB4, ite_true, transpose_one,
      Matrix.one_mul]
    push_cast [hk4, p2_cast]
    have hkj : ((chartKI b.chart : ℤ) : ℝ) = kapJ b.chart := rfl
    simp only [hkj, U, βD, Hm]
    constructor <;> ring

end Cayley.Pack

end
