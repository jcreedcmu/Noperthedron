module

public import Cayley.Soundness.PackSound
public import Cayley.Soundness.KSem

@[expose] public section

/-!
# The gap-leaf polynomials

`gapGen` is generic in the arithmetic, so its integer instance (the checker) and its `PE`
instance (polynomial expressions) are related by evaluation, and so is its real instance.
-/

namespace Cayley.Pack

open Cayley.K

section map

variable {R S : Type} (addR subR mulR : R → R → R) (cR : ℤ → R) (xR : Fin 5 → R)
  (addS subS mulS : S → S → S) (cS : ℤ → S) (xS : Fin 5 → S) (f : R → S)
  (hadd : ∀ a b, f (addR a b) = addS (f a) (f b)) (hsub : ∀ a b, f (subR a b) = subS (f a) (f b))
  (hmul : ∀ a b, f (mulR a b) = mulS (f a) (f b)) (hc : ∀ z, f (cR z) = cS z)
  (hx : ∀ i, f (xR i) = xS i)
include hadd hsub hmul hc

theorem gChart_map (chart : ℕ) (y0 y1 y2 : R) :
    (f (gChart subR mulR cR addR chart y0 y1 y2).1, f (gChart subR mulR cR addR chart y0 y1 y2).2.1,
      f (gChart subR mulR cR addR chart y0 y1 y2).2.2) =
      gChart subS mulS cS addS chart (f y0) (f y1) (f y2) := by
  unfold gChart
  split <;> simp [hadd, hsub, hmul, hc]

omit hadd hsub hmul hc in
theorem gFace_map (face : ℕ) (a b c : R) :
    f (gFace face a b c).1 = (gFace face (f a) (f b) (f c)).1 ∧
      f (gFace face a b c).2.1 = (gFace face (f a) (f b) (f c)).2.1 ∧
      f (gFace face a b c).2.2 = (gFace face (f a) (f b) (f c)).2.2 := by
  unfold gFace; split_ifs <;> simp

include hx in
theorem gapGen_map (b : KBox) (s : ℤ × ℤ × ℤ) (w0 w1 : ℤ) :
    let g := gapGen addR subR mulR cR xR b s w0 w1
    let g' := gapGen addS subS mulS cS xS b s w0 w1
    f g.a0 = g'.a0 ∧ f g.a1 = g'.a1 ∧ f g.a2 = g'.a2 ∧ f g.b0 = g'.b0 ∧ f g.b1 = g'.b1 ∧
      f g.b2 = g'.b2 ∧ f g.kd = g'.kd ∧ f g.l0 = g'.l0 ∧ f g.l1 = g'.l1 ∧ f g.l2 = g'.l2 := by
  intro g g'
  have hgc := gChart_map addR subR mulR cR addS subS mulS cS f hadd hsub hmul hc
  have h1 : ∀ ch y0 y1 y2, f (gChart subR mulR cR addR ch y0 y1 y2).1 =
      (gChart subS mulS cS addS ch (f y0) (f y1) (f y2)).1 := fun ch y0 y1 y2 => by
    rw [← hgc]
  have h2 : ∀ ch y0 y1 y2, f (gChart subR mulR cR addR ch y0 y1 y2).2.1 =
      (gChart subS mulS cS addS ch (f y0) (f y1) (f y2)).2.1 := fun ch y0 y1 y2 => by
    rw [← hgc]
  have h3 : ∀ ch y0 y1 y2, f (gChart subR mulR cR addR ch y0 y1 y2).2.2 =
      (gChart subS mulS cS addS ch (f y0) (f y1) (f y2)).2.2 := fun ch y0 y1 y2 => by
    rw [← hgc]
  have hf1 := fun face a b c => (gFace_map f face a b c).1
  have hf2 := fun face a b c => (gFace_map f face a b c).2.1
  have hf3 := fun face a b c => (gFace_map f face a b c).2.2
  simp only [g, g', gapGen]
  split_ifs <;> simp only [h1, h2, h3, hf1, hf2, hf3, hadd, hsub, hmul, hc, hx, and_self]

end map

/-! ## The real instance -/

open Matrix

/-- The gap-leaf data at a real point `t`. -/
noncomputable def gapR (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (t : Fin 5 → ℝ) : GData ℝ :=
  gapGen (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t b S w0 w1

/-- The integer vertex as a real vector. -/
def svec (S : ℤ × ℤ × ℤ) : Fin 3 → ℝ := ![(S.1 : ℝ), S.2.1, S.2.2]

theorem p2_cast (k : ℕ) : ((p2 k : ℤ) : ℝ) = 2 ^ k := by simp [p2]

/-- The box coordinate in units of `2^-K`. -/
theorem kpt_mul (b : KBox) (t : Fin 5 → ℝ) (i : Fin 5) :
    ((b.c.getD i 0 : ℤ) : ℝ) + ((b.h.getD i 0 : ℤ) : ℝ) * t i = 2 ^ b.K * kpt b t i := by
  simp only [kpt]; field_simp

theorem gapR_alpha (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (t : Fin 5 → ℝ) (y : Fin 3 → ℝ) :
    let g := gapR b S w0 w1 t
    g.a0 * y 0 + g.a1 * y 1 + g.a2 * y 2 = (2 ^ b.K) ^ 2 * lin w0 w1 (NoR (kpt b t) *ᵥ y) := by
  intro g
  have hU : (2 : ℝ) ^ b.K ≠ 0 := by positivity
  have ha : g.a0 = (2 ^ b.K) ^ 2 * (w0 * NoR (kpt b t) 0 0 + w1 * NoR (kpt b t) 1 0) ∧
      g.a1 = (2 ^ b.K) ^ 2 * (w0 * NoR (kpt b t) 0 1 + w1 * NoR (kpt b t) 1 1) ∧
      g.a2 = (2 ^ b.K) ^ 2 * (w0 * NoR (kpt b t) 0 2 + w1 * NoR (kpt b t) 1 2) := by
    simp only [g, gapR, gapGen]
    split_ifs <;> simp only [p2_cast, kpt, NoR, cayleyNumeratorMatrix, of_apply, cons_val',
      cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one, Fin.isValue,
      Fin.val_zero, Fin.val_one, vecHead, vecTail, Function.comp_apply, Fin.succ_zero_eq_one] <;> refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring
  rw [ha.1, ha.2.1, ha.2.2]
  simp only [lin, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The real chart application. -/
theorem gChart_real1 (chart : ℕ) (hj : chart < 5) (y0 y1 y2 : ℝ) :
    (gChart (· - ·) (· * ·) (fun z : ℤ => (z : ℝ)) (· + ·) chart y0 y1 y2).1 =
      ∑ j : Fin 3, chartMR chart 0 j * ![y0, y1, y2] j := by
  interval_cases chart <;> simp [gChart, chartMR, K.chartMI, Fin.sum_univ_three]

theorem gChart_real2 (chart : ℕ) (hj : chart < 5) (y0 y1 y2 : ℝ) :
    (gChart (· - ·) (· * ·) (fun z : ℤ => (z : ℝ)) (· + ·) chart y0 y1 y2).2.1 =
      ∑ j : Fin 3, chartMR chart 1 j * ![y0, y1, y2] j := by
  interval_cases chart <;> simp [gChart, chartMR, K.chartMI, Fin.sum_univ_three]

theorem gChart_real3 (chart : ℕ) (hj : chart < 5) (y0 y1 y2 : ℝ) :
    (gChart (· - ·) (· * ·) (fun z : ℤ => (z : ℝ)) (· + ·) chart y0 y1 y2).2.2 =
      ∑ j : Fin 3, chartMR chart 2 j * ![y0, y1, y2] j := by
  interval_cases chart <;> simp [gChart, chartMR, K.chartMI, Fin.sum_univ_three]

theorem gChart_real (chart : ℕ) (hj : chart < 5) (y0 y1 y2 : ℝ) :
    (gChart (· - ·) (· * ·) (fun z : ℤ => (z : ℝ)) (· + ·) chart y0 y1 y2).1 =
        (chartMR chart *ᵥ ![y0, y1, y2]) 0 ∧
      (gChart (· - ·) (· * ·) (fun z : ℤ => (z : ℝ)) (· + ·) chart y0 y1 y2).2.1 =
        (chartMR chart *ᵥ ![y0, y1, y2]) 1 ∧
      (gChart (· - ·) (· * ·) (fun z : ℤ => (z : ℝ)) (· + ·) chart y0 y1 y2).2.2 =
        (chartMR chart *ᵥ ![y0, y1, y2]) 2 := by
  interval_cases chart <;>
    simp [gChart, chartMR, K.chartMI, mulVec, dotProduct, Fin.sum_univ_three]

/-- The scale of `β`: `U⁴` (blown up) or `U²`. -/
noncomputable def betaSc (b : KBox) : ℝ :=
  if b.chart = 0 ∨ b.chart = 4 then ((2 : ℝ) ^ b.K) ^ 4 else ((2 : ℝ) ^ b.K) ^ 2

theorem kptm2 (b : KBox) (t : Fin 5 → ℝ) :
    ((b.c.getD 2 0 : ℤ) : ℝ) + ((b.h.getD 2 0 : ℤ) : ℝ) * t 2 = 2 ^ b.K * kpt b t 2 := by
  show _ = 2 ^ b.K * ((((b.c.getD 2 0 : ℤ) : ℝ) + ((b.h.getD 2 0 : ℤ) : ℝ) * t 2) / 2 ^ b.K)
  field_simp
theorem kptm3 (b : KBox) (t : Fin 5 → ℝ) :
    ((b.c.getD 3 0 : ℤ) : ℝ) + ((b.h.getD 3 0 : ℤ) : ℝ) * t 3 = 2 ^ b.K * kpt b t 3 := by
  show _ = 2 ^ b.K * ((((b.c.getD 3 0 : ℤ) : ℝ) + ((b.h.getD 3 0 : ℤ) : ℝ) * t 3) / 2 ^ b.K)
  field_simp
theorem kptm4 (b : KBox) (t : Fin 5 → ℝ) :
    ((b.c.getD 4 0 : ℤ) : ℝ) + ((b.h.getD 4 0 : ℤ) : ℝ) * t 4 = 2 ^ b.K * kpt b t 4 := by
  show _ = 2 ^ b.K * ((((b.c.getD 4 0 : ℤ) : ℝ) + ((b.h.getD 4 0 : ℤ) : ℝ) * t 4) / 2 ^ b.K)
  field_simp

theorem kptm (b : KBox) (t : Fin 5 → ℝ) (i : ℕ) (hi : i < 5) :
    ((b.c.getD i 0 : ℤ) : ℝ) + ((b.h.getD i 0 : ℤ) : ℝ) * t ⟨i, hi⟩ = 2 ^ b.K * kpt b t ⟨i, hi⟩ := by
  simp only [kpt]; field_simp

theorem gFace_real (face : ℕ) (U x2 x3 : ℝ) :
    (gFace face (if face % 2 = 0 then U else ((0 : ℤ) : ℝ) - U) (U * x2) (U * x3)).1 =
        U * faceR face x2 x3 0 ∧
      (gFace face (if face % 2 = 0 then U else ((0 : ℤ) : ℝ) - U) (U * x2) (U * x3)).2.1 =
        U * faceR face x2 x3 1 ∧
      (gFace face (if face % 2 = 0 then U else ((0 : ℤ) : ℝ) - U) (U * x2) (U * x3)).2.2 =
        U * faceR face x2 x3 2 := by
  have hsg : (if face % 2 = 0 then U else ((0 : ℤ) : ℝ) - U) =
      U * (if face % 2 = 0 then 1 else -1) := by split_ifs <;> simp
  rw [hsg]
  simp only [gFace, faceR]
  by_cases h0 : face / 2 = 0
  · simp [h0]
  · by_cases h1 : face / 2 = 1
    · simp [h1]
    · obtain ⟨k, hk⟩ : ∃ k, face / 2 = k + 2 := ⟨face / 2 - 2, by omega⟩
      simp [hk]

theorem gapR_beta (b : KBox) (hj : b.chart < 5) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (t : Fin 5 → ℝ) :
    let g := gapR b S w0 w1 t
    let r := rOf (kblow b.chart) b.face (kpt b t)
    let v := chartMR b.chart *ᵥ (cayleyNumeratorMatrix (r 0) (r 1) (r 2) *ᵥ svec S)
    g.b0 = betaSc b * v 0 ∧ g.b1 = betaSc b * v 1 ∧ g.b2 = betaSc b * v 2 ∧
      g.kd = kapJ b.chart * betaSc b * cayleyDenom (r 0) (r 1) (r 2) := by
  intro g r v
  have hF := gFace_real b.face (2 ^ b.K) (kpt b t 2) (kpt b t 3)
  simp only [g, gapR, gapGen, v, r, p2_cast, kptm2, kptm3, kptm4]
  by_cases hbl : b.chart = 0 ∨ b.chart = 4
  · have hk : kblow b.chart = true := by simp [kblow]; exact hbl
    simp only [hbl, ↓reduceIte, hF.1, hF.2.1, hF.2.2, gChart_real1 _ hj, gChart_real2 _ hj,
      gChart_real3 _ hj, betaSc, rOf, hk, svec, kapJ]
    generalize faceR b.face (kpt b t 2) (kpt b t 3) = fv
    generalize kpt b t 4 = ρ
    generalize (2 : ℝ) ^ b.K = U
    simp only [mulVec, dotProduct, Fin.sum_univ_three, cayleyNumeratorMatrix, cayleyDenom,
      Pi.smul_apply, smul_eq_mul, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two,
      empty_val', cons_val_fin_one, vecHead, vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Fin.isValue]
    refine ⟨by ring, by ring, by ring, by ring⟩
  · have hk : kblow b.chart = false := by simp [kblow]; tauto
    simp only [hbl, ↓reduceIte, gChart_real1 _ hj, gChart_real2 _ hj,
      gChart_real3 _ hj, betaSc, rOf, hk, svec, kapJ]
    generalize kpt b t 2 = x2
    generalize kpt b t 3 = x3
    generalize kpt b t 4 = x4
    generalize (2 : ℝ) ^ b.K = U
    simp only [mulVec, dotProduct, Fin.sum_univ_three, cayleyNumeratorMatrix, cayleyDenom,
      of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two,
      empty_val', cons_val_fin_one, vecHead, vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Fin.isValue, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by ring, by ring, by ring, by ring⟩

theorem gapR_L (b : KBox) (hj : b.chart < 5) (hbl : b.chart = 0 ∨ b.chart = 4) (S : ℤ × ℤ × ℤ)
    (w0 w1 : ℤ) (t : Fin 5 → ℝ) :
    let g := gapR b S w0 w1 t
    let c := faceR b.face (kpt b t 2) (kpt b t 3)
    let v := chartMR b.chart *ᵥ (crossR c (svec S) + kpt b t 4 • crossR c (crossR c (svec S)))
    g.l0 = ((2 : ℝ) ^ b.K) ^ 3 * v 0 ∧ g.l1 = ((2 : ℝ) ^ b.K) ^ 3 * v 1 ∧
      g.l2 = ((2 : ℝ) ^ b.K) ^ 3 * v 2 := by
  intro g c v
  have hF := gFace_real b.face (2 ^ b.K) (kpt b t 2) (kpt b t 3)
  simp only [g, gapR, gapGen, v, c, p2_cast, kptm2, kptm3, kptm4, hbl, ↓reduceIte, hF.1, hF.2.1,
    hF.2.2, gChart_real1 _ hj, gChart_real2 _ hj, gChart_real3 _ hj, svec]
  generalize faceR b.face (kpt b t 2) (kpt b t 3) = fv
  generalize kpt b t 4 = ρ
  generalize (2 : ℝ) ^ b.K = U
  simp only [mulVec, dotProduct, Fin.sum_univ_three, crossR, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, cons_val_zero, cons_val_one, cons_val_two,
    cons_val_fin_one, vecHead, vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.isValue]
  refine ⟨by ring, by ring, by ring⟩

/-! ## The three instances -/

/-- The gap-leaf polynomial expressions. -/
def gapPE (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) : GData PE :=
  gapGen PE.add PE.sub PE.mul PE.c PE.x b S w0 w1

/-- A field of the gap data. -/
def _root_.Cayley.K.GData.get {R : Type} (g : GData R) : Fin 10 → R
  | 0 => g.a0 | 1 => g.a1 | 2 => g.a2 | 3 => g.b0 | 4 => g.b1 | 5 => g.b2 | 6 => g.kd
  | 7 => g.l0 | 8 => g.l1 | 9 => g.l2

theorem gapGen_map' {R S : Type} (addR subR mulR : R → R → R) (cR : ℤ → R) (xR : Fin 5 → R)
    (addS subS mulS : S → S → S) (cS : ℤ → S) (xS : Fin 5 → S) (f : R → S)
    (hadd : ∀ a b, f (addR a b) = addS (f a) (f b)) (hsub : ∀ a b, f (subR a b) = subS (f a) (f b))
    (hmul : ∀ a b, f (mulR a b) = mulS (f a) (f b)) (hc : ∀ z, f (cR z) = cS z)
    (hx : ∀ i, f (xR i) = xS i) (b : KBox) (s : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (k : Fin 10) :
    f ((gapGen addR subR mulR cR xR b s w0 w1).get k) =
      (gapGen addS subS mulS cS xS b s w0 w1).get k := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    gapGen_map addR subR mulR cR xR addS subS mulS cS xS f hadd hsub hmul hc hx b s w0 w1
  fin_cases k <;> assumption

theorem gapPE_int (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (k : Fin 10) :
    ((gapPE b S w0 w1).get k).ev (fun i => pX i.val) = (pGapData b S w0 w1).get k :=
  gapGen_map' PE.add PE.sub PE.mul PE.c PE.x Int.add Int.sub Int.mul (fun z => z)
    (fun i => pX i.val) (PE.ev fun i => pX i.val) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => by simp [PE.ev]) (fun _ => rfl) b S w0 w1 k

theorem gapPE_real (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (t : Fin 5 → ℝ) (k : Fin 10) :
    ((gapPE b S w0 w1).get k).ev t = (gapR b S w0 w1 t).get k :=
  gapGen_map' PE.add PE.sub PE.mul PE.c PE.x (· + ·) (· - ·) (· * ·) (fun z => (z : ℝ)) t
    (PE.ev t) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    b S w0 w1 k

theorem gapPE_nrm (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (k : Fin 10) :
    ((gapPE b S w0 w1).get k).nrm = (gapNrm b S w0 w1).get k :=
  gapGen_map' PE.add PE.sub PE.mul PE.c PE.x Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1)
    PE.nrm (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    b S w0 w1 k

/-! ## Degrees -/

/-- Degree bounds of the gap data fields. -/
def degB (k : Fin 10) (i : Fin 5) : ℕ :=
  if k.val < 3 then (if i.val < 2 then 2 else 0)
  else if k.val < 7 then (if i.val < 2 then 0 else 2)
  else (if i.val < 2 then 0 else if i.val = 4 then 1 else 2)

/-- The degree instance of `gapGen`. -/
def gapDeg (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) : GData (Fin 5 → ℕ) :=
  gapGen (fun a c i => max (a i) (c i)) (fun a c i => max (a i) (c i)) (fun a c i => a i + c i)
    (fun _ _ => 0) (fun j i => if j = i then 1 else 0) b S w0 w1

theorem gapPE_deg (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (k : Fin 10) :
    (fun i => ((gapPE b S w0 w1).get k).deg i) = (gapDeg b S w0 w1).get k :=
  gapGen_map' PE.add PE.sub PE.mul PE.c PE.x _ _ _ _ _ (fun e i => e.deg i)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) b S w0 w1 k

/-- Two runs on boxes with the same chart and face, when every constant maps to the same value. -/
theorem gapGen_map2 {R S : Type} (addR subR mulR : R → R → R) (cR : ℤ → R) (xR : Fin 5 → R)
    (addS subS mulS : S → S → S) (cS : ℤ → S) (xS : Fin 5 → S) (f : R → S)
    (hadd : ∀ a b, f (addR a b) = addS (f a) (f b)) (hsub : ∀ a b, f (subR a b) = subS (f a) (f b))
    (hmul : ∀ a b, f (mulR a b) = mulS (f a) (f b)) (hc : ∀ z z', f (cR z) = cS z')
    (hx : ∀ i, f (xR i) = xS i) (b b' : KBox) (hch : b.chart = b'.chart) (hfa : b.face = b'.face)
    (s s' : ℤ × ℤ × ℤ) (w0 w1 w0' w1' : ℤ) (k : Fin 10) :
    f ((gapGen addR subR mulR cR xR b s w0 w1).get k) =
      (gapGen addS subS mulS cS xS b' s' w0' w1').get k := by
  have hc' : ∀ z, f (cR z) = cS z := fun z => hc z z
  have hgc := gChart_map addR subR mulR cR addS subS mulS cS f hadd hsub hmul hc'
  have h1 : ∀ ch y0 y1 y2, f (gChart subR mulR cR addR ch y0 y1 y2).1 =
      (gChart subS mulS cS addS ch (f y0) (f y1) (f y2)).1 := fun ch y0 y1 y2 => by rw [← hgc]
  have h2 : ∀ ch y0 y1 y2, f (gChart subR mulR cR addR ch y0 y1 y2).2.1 =
      (gChart subS mulS cS addS ch (f y0) (f y1) (f y2)).2.1 := fun ch y0 y1 y2 => by rw [← hgc]
  have h3 : ∀ ch y0 y1 y2, f (gChart subR mulR cR addR ch y0 y1 y2).2.2 =
      (gChart subS mulS cS addS ch (f y0) (f y1) (f y2)).2.2 := fun ch y0 y1 y2 => by rw [← hgc]
  have hf1 := fun face a b c => (gFace_map f face a b c).1
  have hf2 := fun face a b c => (gFace_map f face a b c).2.1
  have hf3 := fun face a b c => (gFace_map f face a b c).2.2
  have hcc : ∀ z z', cS z = cS z' := fun z z' => by rw [← hc z z', hc z z]
  simp only [gapGen, hch, hfa]
  split_ifs <;> fin_cases k <;>
    simp only [K.GData.get, h1, h2, h3, hf1, hf2, hf3, hadd, hsub, hmul, hc', hx] <;>
    simp only [hcc _ 0]

theorem gapDeg_data (b : KBox) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ) (k : Fin 10) :
    (gapDeg b S w0 w1).get k = (gapDeg ⟨b.chart, b.face, 0, [], []⟩ (0, 0, 0) 0 0).get k := by
  unfold gapDeg
  exact gapGen_map2 (R := Fin 5 → ℕ) (S := Fin 5 → ℕ) (fun a c i => max (a i) (c i)) (fun a c i => max (a i) (c i)) (fun a c i => a i + c i)
    (fun _ _ => 0) (fun j i => if j = i then 1 else 0)
    (fun a c i => max (a i) (c i)) (fun a c i => max (a i) (c i)) (fun a c i => a i + c i)
    (fun _ _ => 0) (fun j i => if j = i then 1 else 0) id (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) b ⟨b.chart, b.face, 0, [], []⟩ rfl rfl S
    (0, 0, 0) w0 w1 0 0 k

theorem gapDeg_closed : ∀ chart < 5, ∀ face < 6, ∀ k : Fin 10, ∀ i : Fin 5,
    (gapDeg ⟨chart, face, 0, [], []⟩ (0, 0, 0) 0 0).get k i ≤ degB k i := by
  decide +kernel

theorem gapDeg_le (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) (S : ℤ × ℤ × ℤ) (w0 w1 : ℤ)
    (k : Fin 10) (i : Fin 5) : (gapDeg b S w0 w1).get k i ≤ degB k i := by
  rw [gapDeg_data]; exact gapDeg_closed _ hj _ hf k i

end Cayley.Pack