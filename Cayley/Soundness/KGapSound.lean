module

public import Cayley.Soundness.KGapPoly
public import Cayley.Soundness.KVtx
public import Cayley.Soundness.PackBern

@[expose] public section

/-!
# Soundness of the kernel gap leaf

`pGapOK b s w₀ w₁ = true` implies, at every point of the box, the hypotheses of `gap_core`.
-/

namespace Cayley.Pack

set_option exponentiation.threshold 1024

open Cayley.K Noperthedron
open scoped Matrix

/-! ## The vertex table -/

/-- The kernel vertex table is the checker's `vertexTab`, scaled by `2^160`. -/
theorem vt_scaled' : ∀ t < 90,
    (vertexOf (t / 6) (t % 6 / 3) (t % 3)).x.e ≤ 160 ∧ (vertexOf (t / 6) (t % 6 / 3) (t % 3)).y.e ≤ 160 ∧
      (vertexOf (t / 6) (t % 6 / 3) (t % 3)).z.e ≤ 160 ∧
      (vertexOf (t / 6) (t % 6 / 3) (t % 3)).x.m *
        2 ^ (160 - (vertexOf (t / 6) (t % 6 / 3) (t % 3)).x.e) = (vt t).1 ∧
      (vertexOf (t / 6) (t % 6 / 3) (t % 3)).y.m *
        2 ^ (160 - (vertexOf (t / 6) (t % 6 / 3) (t % 3)).y.e) = (vt t).2.1 ∧
      (vertexOf (t / 6) (t % 6 / 3) (t % 3)).z.m *
        2 ^ (160 - (vertexOf (t / 6) (t % 6 / 3) (t % 3)).z.e) = (vt t).2.2 := by
  decide +kernel

theorem vertexTab_eq (t : ℕ) (ht : t < 90) : vertexTab[t]! = vertexOf (t / 6) (t % 6 / 3) (t % 3) := by
  simp [vertexTab, getElem!_pos, ht]

theorem vt_scaled (t : ℕ) (ht : t < 90) :
    (vertexTab[t]!).x.e ≤ 160 ∧ (vertexTab[t]!).y.e ≤ 160 ∧ (vertexTab[t]!).z.e ≤ 160 ∧
      (vertexTab[t]!).x.m * 2 ^ (160 - (vertexTab[t]!).x.e) = (vt t).1 ∧
      (vertexTab[t]!).y.m * 2 ^ (160 - (vertexTab[t]!).y.e) = (vt t).2.1 ∧
      (vertexTab[t]!).z.m * 2 ^ (160 - (vertexTab[t]!).z.e) = (vt t).2.2 := by
  rw [vertexTab_eq t ht]; exact vt_scaled' t ht

theorem D_scaled {q : QI} {m : ℤ} (he : q.e ≤ 160) (hm : q.m * 2 ^ (160 - q.e) = m) :
    D q = (m : ℝ) / 2 ^ 160 := by
  rw [← hm, D]
  push_cast
  rw [show (2 : ℝ) ^ 160 = 2 ^ q.e * 2 ^ (160 - q.e) by rw [← pow_add]; congr 1; omega]
  field_simp

/-- The tabulated vertex as a real vector. -/
noncomputable def vR (t : ℕ) : Fin 3 → ℝ := fun i => svec (vt t) i / 2 ^ 160

theorem vR_err {t : ℕ} (ht : t < 90) : ∀ i, |(vtx t - vR t) i| ≤ 1 / 2 ^ 60 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vt_scaled t ht
  have he : vR t = (vertexTab[t]!).toR := by
    funext i
    fin_cases i <;> simp [vR, svec, V3.toR, D_scaled h1 h4, D_scaled h2 h5, D_scaled h3 h6]
  intro i
  rw [he]
  have := vertex_approx t ht i
  rwa [D_errε] at this

/-! ## The decoded polynomials -/

section polys

variable (b : KBox) (s : ℕ) (w0 w1 : ℤ)

/-- The gap-leaf expressions for inner vertex `s`. -/
def gp : GData PE := gapPE b (vt s) w0 w1

/-- `A = Σ αₖ βₖ`. -/
def Ap : PE := PE.add (PE.add (PE.mul (gp b s w0 w1).a0 (gp b s w0 w1).b0)
  (PE.mul (gp b s w0 w1).a1 (gp b s w0 w1).b1)) (PE.mul (gp b s w0 w1).a2 (gp b s w0 w1).b2)

/-- `Eₖ = αₖ κD`. -/
def Ep0 : PE := PE.mul (gp b s w0 w1).a0 (gp b s w0 w1).kd
def Ep1 : PE := PE.mul (gp b s w0 w1).a1 (gp b s w0 w1).kd
def Ep2 : PE := PE.mul (gp b s w0 w1).a2 (gp b s w0 w1).kd

/-- `Σ Tₖ αₖ`. -/
def xp (T : ℤ × ℤ × ℤ) : PE :=
  PE.add (PE.add (PE.mul (PE.c T.1) (gp b s w0 w1).a0) (PE.mul (PE.c T.2.1) (gp b s w0 w1).a1))
    (PE.mul (PE.c T.2.2) (gp b s w0 w1).a2)

/-- `F_T = A − (Σ Tₖ αₖ) κD`. -/
def Fp (T : ℤ × ℤ × ℤ) : PE := PE.sub (Ap b s w0 w1) (PE.mul (xp b s w0 w1 T) (gp b s w0 w1).kd)

/-- `L = Σ αₖ Lₖ`. -/
def Lp : PE := PE.add (PE.add (PE.mul (gp b s w0 w1).a0 (gp b s w0 w1).l0)
  (PE.mul (gp b s w0 w1).a1 (gp b s w0 w1).l1)) (PE.mul (gp b s w0 w1).a2 (gp b s w0 w1).l2)

/-- Field values of `gp`. -/
theorem gp_int (k : Fin 10) :
    ((gp b s w0 w1).get k).ev (fun i => pX i.val) = (pGapData b (vt s) w0 w1).get k :=
  gapPE_int b (vt s) w0 w1 k

theorem gp_real (t : Fin 5 → ℝ) (k : Fin 10) :
    ((gp b s w0 w1).get k).ev t = (gapR b (vt s) w0 w1 t).get k :=
  gapPE_real b (vt s) w0 w1 t k

theorem gp_fields_real (t : Fin 5 → ℝ) :
    let g := gapR b (vt s) w0 w1 t
    (gp b s w0 w1).a0.ev t = g.a0 ∧ (gp b s w0 w1).a1.ev t = g.a1 ∧ (gp b s w0 w1).a2.ev t = g.a2 ∧
    (gp b s w0 w1).b0.ev t = g.b0 ∧ (gp b s w0 w1).b1.ev t = g.b1 ∧ (gp b s w0 w1).b2.ev t = g.b2 ∧
    (gp b s w0 w1).kd.ev t = g.kd ∧ (gp b s w0 w1).l0.ev t = g.l0 ∧
    (gp b s w0 w1).l1.ev t = g.l1 ∧ (gp b s w0 w1).l2.ev t = g.l2 :=
  ⟨gp_real b s w0 w1 t 0, gp_real b s w0 w1 t 1, gp_real b s w0 w1 t 2, gp_real b s w0 w1 t 3,
    gp_real b s w0 w1 t 4, gp_real b s w0 w1 t 5, gp_real b s w0 w1 t 6, gp_real b s w0 w1 t 7,
    gp_real b s w0 w1 t 8, gp_real b s w0 w1 t 9⟩

theorem gapSc_eq (b : KBox) : (2 : ℝ) ^ gapSc b = ((2 : ℝ) ^ b.K) ^ 2 * betaSc b := by
  unfold gapSc betaSc
  split_ifs <;> simp only [← pow_mul, ← pow_add] <;> congr 1 <;> ring

/-- The real value of `F_T`: the scaled gap of the tabulated vertices. -/
theorem Fp_real (hj : b.chart < 5) (t : Fin 5 → ℝ) (T : ℤ × ℤ × ℤ) :
    (Fp b s w0 w1 T).ev t = 2 ^ gapSc b * 2 ^ 160 *
      (cayleyDenom (kpt b t 1) (-kpt b t 0) 0 * kapJ b.chart *
        cayleyDenom (rOf (kblow b.chart) b.face (kpt b t) 0) (rOf (kblow b.chart) b.face (kpt b t) 1)
          (rOf (kblow b.chart) b.face (kpt b t) 2) *
        (lin w0 w1 ((outerRot (kpt b t 0) (kpt b t 1) * Qm b.chart (rOf (kblow b.chart) b.face (kpt b t)))
            *ᵥ vR s) -
          lin w0 w1 (outerRot (kpt b t 0) (kpt b t 1) *ᵥ fun i => svec T i / 2 ^ 160))) := by
  obtain ⟨ha0, ha1, ha2, hb0, hb1, hb2, hkd, -, -, -⟩ := gp_fields_real b s w0 w1 t
  obtain ⟨eb0, eb1, eb2, ekd⟩ := gapR_beta b hj (vt s) w0 w1 t
  have hNo : NoR (kpt b t) = cayleyDenom (kpt b t 1) (-kpt b t 0) 0 • outerRot (kpt b t 0) (kpt b t 1) :=
    cayleyNumeratorMatrix_eq_denom_smul _ _ _
  set r := rOf (kblow b.chart) b.face (kpt b t)
  set g := gapR b (vt s) w0 w1 t
  set v := chartMR b.chart *ᵥ (cayleyNumeratorMatrix (r 0) (r 1) (r 2) *ᵥ svec (vt s))
  have hα1 := gapR_alpha b (vt s) w0 w1 t (betaSc b • v)
  have hα2 := gapR_alpha b (vt s) w0 w1 t (svec T)
  simp only [Pi.smul_apply, smul_eq_mul] at hα1
  have e : (Fp b s w0 w1 T).ev t =
      (g.a0 * (betaSc b * v 0) + g.a1 * (betaSc b * v 1) + g.a2 * (betaSc b * v 2)) -
        (g.a0 * svec T 0 + g.a1 * svec T 1 + g.a2 * svec T 2) *
          (kapJ b.chart * betaSc b * cayleyDenom (r 0) (r 1) (r 2)) := by
    simp only [Fp, Ap, xp, PE.ev, ha0, ha1, ha2, hb0, hb1, hb2, hkd, eb0, eb1, eb2, ekd, svec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  rw [e, hα1, hα2, gapSc_eq]
  have hN : cayleyNumeratorMatrix (r 0) (r 1) (r 2) = cayleyDenom (r 0) (r 1) (r 2) • cayV r :=
    cayleyNumeratorMatrix_eq_denom_smul _ _ _
  have hM := chartMR_eq b.chart hj
  have hS : svec (vt s) = (2 : ℝ) ^ 160 • vR s := by
    funext i; simp only [vR, Pi.smul_apply, smul_eq_mul]; field_simp
  have hT : svec T = (2 : ℝ) ^ 160 • (fun i => svec T i / 2 ^ 160) := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  simp only [v, hNo, hN, hM, hS, Qm]
  conv_lhs => rw [hT]
  simp only [lin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul, Pi.smul_apply]
  ring

/-- The real value of `L` (blown-up charts): the scaled paired-vertex bracket. -/
theorem Lp_real (hj : b.chart < 5) (hbl : b.chart = 0 ∨ b.chart = 4) (t : Fin 5 → ℝ) :
    2 * (Lp b s w0 w1).ev t = 2 ^ gapScL b * 2 ^ 160 *
      (2 * lin w0 w1 (NoR (kpt b t) *ᵥ (chartMR b.chart *ᵥ
        (crossR (faceR b.face (kpt b t 2) (kpt b t 3)) (vR s) +
          kpt b t 4 • crossR (faceR b.face (kpt b t 2) (kpt b t 3))
            (crossR (faceR b.face (kpt b t 2) (kpt b t 3)) (vR s)))))) := by
  obtain ⟨ha0, ha1, ha2, -, -, -, -, hl0, hl1, hl2⟩ := gp_fields_real b s w0 w1 t
  obtain ⟨el0, el1, el2⟩ := gapR_L b hj hbl (vt s) w0 w1 t
  set g := gapR b (vt s) w0 w1 t
  set c := faceR b.face (kpt b t 2) (kpt b t 3)
  set v := chartMR b.chart *ᵥ (crossR c (svec (vt s)) + kpt b t 4 • crossR c (crossR c (svec (vt s))))
  have hα := gapR_alpha b (vt s) w0 w1 t (((2 : ℝ) ^ b.K) ^ 3 • v)
  simp only [Pi.smul_apply, smul_eq_mul] at hα
  have e : (Lp b s w0 w1).ev t = g.a0 * ((2 ^ b.K) ^ 3 * v 0) + g.a1 * ((2 ^ b.K) ^ 3 * v 1) +
      g.a2 * ((2 ^ b.K) ^ 3 * v 2) := by
    simp only [Lp, PE.ev, ha0, ha1, ha2, hl0, hl1, hl2, el0, el1, el2]
  have hS : svec (vt s) = (2 : ℝ) ^ 160 • vR s := by
    funext i; simp only [vR, Pi.smul_apply, smul_eq_mul]; field_simp
  have hsc : (2 : ℝ) ^ gapScL b = ((2 : ℝ) ^ b.K) ^ 2 * ((2 : ℝ) ^ b.K) ^ 3 := by
    unfold gapScL; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e, hα, hsc]
  simp only [v, hS, crossR_smul_right, smul_add, Matrix.mulVec_smul, Matrix.mulVec_add]
  simp only [lin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  ring

/-! ### Degrees and norms -/

theorem gp_deg (hj : b.chart < 5) (hf : b.face < 6) (k : Fin 10) (i : Fin 5) :
    ((gp b s w0 w1).get k).deg i ≤ degB k i := by
  have h := congrFun (gapPE_deg b (vt s) w0 w1 k) i
  rw [gp]; exact h ▸ gapDeg_le b hj hf _ _ _ k i

theorem fits_all (hj : b.chart < 5) (hf : b.face < 6) (T : ℤ × ℤ × ℤ) :
    L3.Fits (Ap b s w0 w1) ∧ L3.Fits (Ep0 b s w0 w1) ∧ L3.Fits (Ep1 b s w0 w1) ∧
      L3.Fits (Ep2 b s w0 w1) ∧ L3.Fits (Fp b s w0 w1 T) ∧ L3.Fits (Lp b s w0 w1) := by
  have hd := gp_deg b s w0 w1 hj hf
  have d : ∀ k i, ((gp b s w0 w1).get k).deg i ≤ degB k i := hd
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · have h0 := d 0 i; have h1 := d 1 i; have h2 := d 2 i; have h3 := d 3 i; have h4 := d 4 i
    have h5 := d 5 i; have h6 := d 6 i; have h7 := d 7 i; have h8 := d 8 i; have h9 := d 9 i
    simp only [K.GData.get] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp only [Ap, Ep0, Ep1, Ep2, Fp, xp, Lp, PE.deg, L3]
    fin_cases i <;> simp [degB] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢ <;> omega

theorem O_eq : O = 2 ^ 399 := by unfold O; norm_num [PW]

theorem nrm_add' (a c : PE) : (PE.add a c).nrm = a.nrm + c.nrm := rfl
theorem nrm_sub' (a c : PE) : (PE.sub a c).nrm = a.nrm + c.nrm := rfl
theorem nrm_mul' (a c : PE) : (PE.mul a c).nrm = a.nrm * c.nrm := rfl
theorem nrm_c' (z : ℤ) : (PE.c z).nrm = z.natAbs := rfl

theorem gapNrmOK_spec {b : KBox} {S : ℤ × ℤ × ℤ} {w0 w1 : ℤ} (h : gapNrmOK b S w0 w1 = true) :
    (gapNrm b S w0 w1).a0 * (gapNrm b S w0 w1).b0 + (gapNrm b S w0 w1).a1 * (gapNrm b S w0 w1).b1 +
        (gapNrm b S w0 w1).a2 * (gapNrm b S w0 w1).b2 +
        2 ^ 161 * ((gapNrm b S w0 w1).a0 + (gapNrm b S w0 w1).a1 + (gapNrm b S w0 w1).a2) *
          (gapNrm b S w0 w1).kd < 2 ^ 390 ∧
      (gapNrm b S w0 w1).a0 * (gapNrm b S w0 w1).l0 + (gapNrm b S w0 w1).a1 * (gapNrm b S w0 w1).l1 +
        (gapNrm b S w0 w1).a2 * (gapNrm b S w0 w1).l2 < 2 ^ 390 := by
  unfold gapNrmOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem nrm_all390 (h : gapNrmOK b (vt s) w0 w1 = true) (T : ℤ × ℤ × ℤ)
    (hT : T.1.natAbs < 2 ^ 161 ∧ T.2.1.natAbs < 2 ^ 161 ∧ T.2.2.natAbs < 2 ^ 161) :
    (Ap b s w0 w1).nrm < 2 ^ 390 ∧ (Ep0 b s w0 w1).nrm < 2 ^ 390 ∧ (Ep1 b s w0 w1).nrm < 2 ^ 390 ∧
      (Ep2 b s w0 w1).nrm < 2 ^ 390 ∧ (Fp b s w0 w1 T).nrm < 2 ^ 390 ∧
        (Lp b s w0 w1).nrm < 2 ^ 390 := by
  have hn : ∀ k, ((gp b s w0 w1).get k).nrm = (gapNrm b (vt s) w0 w1).get k :=
    gapPE_nrm b (vt s) w0 w1
  have n0 := hn 0; have n1 := hn 1; have n2 := hn 2; have n3 := hn 3; have n4 := hn 4
  have n5 := hn 5; have n6 := hn 6; have n7 := hn 7; have n8 := hn 8; have n9 := hn 9
  simp only [K.GData.get] at n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
  obtain ⟨hA, hL⟩ := gapNrmOK_spec h
  set nb := gapNrm b (vt s) w0 w1
  simp only [Ap, Ep0, Ep1, Ep2, Fp, Lp, xp, nrm_add', nrm_sub', nrm_mul', nrm_c', n0, n1, n2, n3,
    n4, n5, n6, n7, n8, n9]
  obtain ⟨t1, t2, t3⟩ := hT
  clear h hn n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
  clear_value nb
  have hP : 1 ≤ (2 : ℕ) ^ 161 := Nat.one_le_two_pow
  generalize (2 : ℕ) ^ 161 = P at *
  generalize (2 : ℕ) ^ 390 = Q at *
  generalize nb.a0 = a0 at *
  generalize nb.a1 = a1 at *
  generalize nb.a2 = a2 at *
  generalize nb.kd = kd at *
  have hx : T.1.natAbs * a0 + T.2.1.natAbs * a1 + T.2.2.natAbs * a2 ≤ (a0 + a1 + a2) * P := by
    have := Nat.mul_le_mul_right a0 t1.le; have := Nat.mul_le_mul_right a1 t2.le
    have := Nat.mul_le_mul_right a2 t3.le; nlinarith
  rw [mul_comm P] at hA
  have h0 : a0 * kd ≤ (a0 + a1 + a2) * P * kd := Nat.mul_le_mul_right _ (by nlinarith)
  have h1 : a1 * kd ≤ (a0 + a1 + a2) * P * kd := Nat.mul_le_mul_right _ (by nlinarith)
  have h2 : a2 * kd ≤ (a0 + a1 + a2) * P * kd := Nat.mul_le_mul_right _ (by nlinarith)
  have h3 := Nat.mul_le_mul_right kd hx
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem two390_lt_O : (2 : ℕ) ^ 390 < O := by
  rw [O_eq]; exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)

theorem nrm_all (h : gapNrmOK b (vt s) w0 w1 = true) (T : ℤ × ℤ × ℤ)
    (hT : T.1.natAbs < 2 ^ 161 ∧ T.2.1.natAbs < 2 ^ 161 ∧ T.2.2.natAbs < 2 ^ 161) :
    (Ap b s w0 w1).nrm < O ∧ (Ep0 b s w0 w1).nrm < O ∧ (Ep1 b s w0 w1).nrm < O ∧
      (Ep2 b s w0 w1).nrm < O ∧ (Fp b s w0 w1 T).nrm < O ∧ (Lp b s w0 w1).nrm < O := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := nrm_all390 b s w0 w1 h T hT
  have := two390_lt_O
  exact ⟨h1.trans this, h2.trans this, h3.trans this, h4.trans this, h5.trans this, h6.trans this⟩

/-- Room for the Bernstein transform: `243 n + 2^390 ≤ O` when `n < 2^390`, and for `2n`. -/
theorem bern_room {n : ℕ} (h : n < 2 ^ 390) : 243 * (n : ℤ) + 2 ^ 390 ≤ O ∧
    243 * ((2 * n : ℕ) : ℤ) + 2 ^ 390 ≤ O := by
  have hO : (O : ℤ) = 512 * 2 ^ 390 := by
    rw [O_eq]; push_cast
  have h' : (n : ℤ) < 2 ^ 390 := by exact_mod_cast h
  rw [hO]; push_cast
  generalize (2 : ℤ) ^ 390 = Q at *
  constructor <;> omega

end polys

/-! ## The vertex-packed quick test -/

theorem testBit_top {x n : ℕ} (hx : x < 2 ^ (n + 1)) : x.testBit n = decide (2 ^ n ≤ x) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have h2 : x / 2 ^ n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]; rw [pow_succ] at hx; linarith
  by_cases h : 2 ^ n ≤ x
  · have : x / 2 ^ n = 1 := by
      have : 1 ≤ x / 2 ^ n := (Nat.le_div_iff_mul_le (Nat.two_pow_pos n)).2 (by rw [one_mul]; exact h)
      omega
    simp [this, h]
  · have : x / 2 ^ n = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

/-- One table term of the packed sum. -/
theorem tab_eq (e : ℤ) (tn tp : ℕ) (dn dp : ℕ → ℕ) (hn : tn = packN 640 dn 90)
    (hp : tp = packN 640 dp 90) :
    (if 0 ≤ e then tn else tp) * e.natAbs =
      packN 640 (fun t => e.natAbs * (if 0 ≤ e then dn t else dp t)) 90 := by
  rw [mul_comm]; split_ifs <;> simp only [hn, hp, packN_mul_left]

/-- Its slot `t`. -/
def quickDig (C e00 e01 e02 : ℤ) (n0 n1 n2 : ℕ) (t : ℕ) : ℕ :=
  C.toNat * 1 + e00.natAbs * (if 0 ≤ e00 then ((BT : ℤ) - (vt t).1).toNat else ((vt t).1 + BT).toNat) +
    (e01.natAbs * (if 0 ≤ e01 then ((BT : ℤ) - (vt t).2.1).toNat else ((vt t).2.1 + BT).toNat) +
      e02.natAbs * (if 0 ≤ e02 then ((BT : ℤ) - (vt t).2.2).toNat else ((vt t).2.2 + BT).toNat)) +
    (n0 * (BT - (vt t).1.natAbs) + (n1 * (BT - (vt t).2.1.natAbs) + n2 * (BT - (vt t).2.2.natAbs)))

theorem quickV_eq (C e00 e01 e02 : ℤ) (n0 n1 n2 : ℕ) :
    quickV C e00 e01 e02 n0 n1 n2 = packN 640 (quickDig C e00 e01 e02 n0 n1 n2) 90 := by
  simp only [quickV, Nat.add_eq, Nat.mul_eq]
  rw [tab_eq e00 tnx tpx _ _ tnx_eq tpx_eq, tab_eq e01 tny tpy _ _ tny_eq tpy_eq,
    tab_eq e02 tnz tpz _ _ tnz_eq tpz_eq, onesT_eq, tax_eq, tay_eq, taz_eq]
  simp only [mul_comm _ C.toNat, mul_comm _ n0, mul_comm _ n1, mul_comm _ n2, packN_mul_left,
    ← packN_add]
  rfl

/-- The slot as an integer. -/
theorem quickDig_int (C e00 e01 e02 : ℤ) (n0 n1 n2 : ℕ) (hC : 0 ≤ C) {t : ℕ} (ht : t < 90) :
    (quickDig C e00 e01 e02 n0 n1 n2 t : ℤ) = C + (BT : ℤ) * ((e00.natAbs + e01.natAbs + e02.natAbs : ℕ) +
      (n0 + n1 + n2 : ℕ)) - ((vt t).1 * e00 + (vt t).2.1 * e01 + (vt t).2.2 * e02) -
      ((vt t).1.natAbs * n0 + (vt t).2.1.natAbs * n1 + (vt t).2.2.natAbs * n2 : ℕ) := by
  obtain ⟨b1, b2, b3⟩ := vt_bound t ht
  have hB : (2 : ℕ) ^ 161 ≤ BT := by unfold BT; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have term : ∀ (e T : ℤ), T.natAbs < 2 ^ 161 →
      |e| * (if 0 ≤ e then ((((BT : ℤ) - T).toNat : ℕ) : ℤ) else (((T + BT).toNat : ℕ) : ℤ)) =
        (BT : ℤ) * |e| - T * e := by
    intro e T hT
    have hT' : |T| < (BT : ℤ) := by
      have : (T.natAbs : ℤ) < BT := by exact_mod_cast lt_of_lt_of_le hT hB
      rwa [Int.natCast_natAbs] at this
    have := abs_lt.1 hT'
    split_ifs with he
    · rw [Int.toNat_of_nonneg (by linarith), abs_of_nonneg he]; ring
    · rw [Int.toNat_of_nonneg (by linarith), abs_of_neg (by linarith)]; ring
  have term2 : ∀ (n : ℕ) (T : ℤ), T.natAbs < 2 ^ 161 →
      (n : ℤ) * ((BT - T.natAbs : ℕ) : ℤ) = (BT : ℤ) * n - |T| * n := by
    intro n T hT
    have : T.natAbs ≤ BT := le_trans hT.le hB
    rw [Nat.cast_sub this, Int.natCast_natAbs]; ring
  simp only [quickDig]
  push_cast
  rw [term e00 _ b1, term e01 _ b2, term e02 _ b3, term2 n0 _ b1, term2 n1 _ b2, term2 n2 _ b3,
    Int.toNat_of_nonneg hC]
  ring

theorem quick_bit (q e00 e01 e02 : ℤ) (n0 n1 n2 : ℕ)
    (hC : 0 ≤ p2 639 + q - p2 170 * (((e00.natAbs : ℤ) + e01.natAbs + e02.natAbs) +
      ((n0 : ℤ) + n1 + n2)))
    (hC2 : p2 639 + q - p2 170 * (((e00.natAbs : ℤ) + e01.natAbs + e02.natAbs) + ((n0 : ℤ) + n1 + n2)) +
      2 * p2 170 * (((e00.natAbs : ℤ) + e01.natAbs + e02.natAbs) + ((n0 : ℤ) + n1 + n2)) < p2 640)
    {t : ℕ} (ht : t < 90)
    (hb : (quickV (p2 639 + q - p2 170 * (((e00.natAbs : ℤ) + e01.natAbs + e02.natAbs) +
      ((n0 : ℤ) + n1 + n2))) e00 e01 e02 n0 n1 n2).testBit (640 * t + 639) = true) :
    0 ≤ q - ((vt t).1 * e00 + (vt t).2.1 * e01 + (vt t).2.2 * e02) -
      ((vt t).1.natAbs * n0 + (vt t).2.1.natAbs * n1 + (vt t).2.2.natAbs * n2 : ℕ) := by
  set C := p2 639 + q - p2 170 * (((e00.natAbs : ℤ) + e01.natAbs + e02.natAbs) + ((n0 : ℤ) + n1 + n2))
  have hBT : (p2 170 : ℤ) = BT := by simp [p2, BT]
  have hdig : ∀ j < 90, quickDig C e00 e01 e02 n0 n1 n2 j < 2 ^ 640 := by
    intro j hj
    have e := quickDig_int C e00 e01 e02 n0 n1 n2 hC hj
    obtain ⟨b1, b2, b3⟩ := vt_bound j hj
    have hB : (2 : ℕ) ^ 161 ≤ BT := by unfold BT; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have k : ∀ (e T : ℤ), T.natAbs < 2 ^ 161 → -(T * e) ≤ BT * e.natAbs := by
      intro e T hT
      have : (T.natAbs : ℤ) ≤ BT := by exact_mod_cast le_trans hT.le hB
      have h1 : -(T * e) ≤ |T * e| := neg_le_abs _
      rw [abs_mul] at h1
      have h2 : |T| * |e| ≤ BT * |e| := mul_le_mul_of_nonneg_right (by rwa [Int.natCast_natAbs] at this)
        (abs_nonneg _)
      simp only [Int.natCast_natAbs]; linarith
    have k1 := k e00 _ b1; have k2 := k e01 _ b2; have k3 := k e02 _ b3
    have hp : (p2 640 : ℤ) = ((2 ^ 640 : ℕ) : ℤ) := rfl
    rw [hBT] at hC2
    have : (quickDig C e00 e01 e02 n0 n1 n2 j : ℤ) < ((2 ^ 640 : ℕ) : ℤ) := by
      rw [e, ← hp]
      push_cast at *
      have hn : 0 ≤ |(vt j).1| * (n0 : ℤ) + |(vt j).2.1| * n1 + |(vt j).2.2| * n2 := by positivity
      have hBT0 : (0 : ℤ) ≤ BT := by positivity
      have hS : (BT : ℤ) * (|e00| + |e01| + |e02|) ≤
          BT * (|e00| + |e01| + |e02| + ((n0 : ℤ) + n1 + n2)) :=
        mul_le_mul_of_nonneg_left (by have : (0 : ℤ) ≤ (n0 : ℤ) + n1 + n2 := by positivity
                                      linarith) hBT0
      linarith
    exact_mod_cast this
  rw [quickV_eq, testBit_packN hdig] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨-, hb⟩ := hb
  have h1 : (640 * t + 639) / 640 = t := by omega
  have h2 : (640 * t + 639) % 640 = 639 := by omega
  rw [h1, h2, testBit_top (hdig t ht)] at hb
  simp only [decide_eq_true_eq] at hb
  have e := quickDig_int C e00 e01 e02 n0 n1 n2 hC ht
  have hb' : ((2 ^ 639 : ℕ) : ℤ) ≤ (quickDig C e00 e01 e02 n0 n1 n2 t : ℤ) := by exact_mod_cast hb
  rw [e, ← hBT] at hb'
  simp only [C, p2] at hb'
  push_cast at hb' ⊢
  linarith

/-! ## Per-vertex bounds -/

theorem quick_real {A E0 E1 E2 c0 sl e0 e1 e2 a0 a1 a2 T0 T1 T2 err : ℝ} (hA : c0 - sl ≤ A)
    (h0 : |E0 - e0| ≤ a0) (h1 : |E1 - e1| ≤ a1) (h2 : |E2 - e2| ≤ a2)
    (hq : 0 ≤ c0 - sl - err - (T0 * e0 + T1 * e1 + T2 * e2) - (|T0| * a0 + |T1| * a1 + |T2| * a2)) :
    err ≤ A - (T0 * E0 + T1 * E1 + T2 * E2) := by
  have k : ∀ T E e a : ℝ, |E - e| ≤ a → T * E ≤ T * e + |T| * a := by
    intro T E e a h
    have : T * (E - e) ≤ |T| * a := by
      calc T * (E - e) ≤ |T * (E - e)| := le_abs_self _
        _ = |T| * |E - e| := abs_mul _ _
        _ ≤ |T| * a := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    linarith
  linarith [k T0 E0 e0 a0 h0, k T1 E1 e1 a1 h1, k T2 E2 e2 a2 h2]

section leaf

variable (b : KBox) (s : ℕ) (w0 w1 : ℤ)

/-- The Kronecker point as a function. -/
abbrev pXv : Fin 5 → ℤ := fun i => pX i.val

theorem gp_fields_int :
    let g := pGapData b (vt s) w0 w1
    (gp b s w0 w1).a0.ev pXv = g.a0 ∧ (gp b s w0 w1).a1.ev pXv = g.a1 ∧
    (gp b s w0 w1).a2.ev pXv = g.a2 ∧ (gp b s w0 w1).b0.ev pXv = g.b0 ∧
    (gp b s w0 w1).b1.ev pXv = g.b1 ∧ (gp b s w0 w1).b2.ev pXv = g.b2 ∧
    (gp b s w0 w1).kd.ev pXv = g.kd ∧ (gp b s w0 w1).l0.ev pXv = g.l0 ∧
    (gp b s w0 w1).l1.ev pXv = g.l1 ∧ (gp b s w0 w1).l2.ev pXv = g.l2 :=
  ⟨gp_int b s w0 w1 0, gp_int b s w0 w1 1, gp_int b s w0 w1 2, gp_int b s w0 w1 3,
    gp_int b s w0 w1 4, gp_int b s w0 w1 5, gp_int b s w0 w1 6, gp_int b s w0 w1 7,
    gp_int b s w0 w1 8, gp_int b s w0 w1 9⟩

theorem ints :
    let g := pGapData b (vt s) w0 w1
    gA g = (Ap b s w0 w1).ev pXv ∧ gL g = (Lp b s w0 w1).ev pXv ∧
      Int.mul g.a0 g.kd = (Ep0 b s w0 w1).ev pXv ∧ Int.mul g.a1 g.kd = (Ep1 b s w0 w1).ev pXv ∧
      Int.mul g.a2 g.kd = (Ep2 b s w0 w1).ev pXv ∧
      ∀ T : ℤ × ℤ × ℤ, gF g T.1 T.2.1 T.2.2 = (Fp b s w0 w1 T).ev pXv := by
  intro g
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := gp_fields_int b s w0 w1
  refine ⟨?_, ?_, ?_, ?_, ?_, fun T => ?_⟩ <;>
    simp only [gA, gL, gF, Ap, Lp, Ep0, Ep1, Ep2, Fp, xp, PE.ev, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, Int.cast_id] <;> rfl

/-- The error scale: `err ≤ F_T` at a point gives the per-vertex hypothesis of `gap_core`. -/
theorem err_scale {sc : ℕ} {Y : ℝ} (j : ℕ)
    (h : ((128 * chartKI j * ((w0.natAbs : ℤ) + w1.natAbs) * p2 (sc + 100) : ℤ) : ℝ) ≤
      2 ^ sc * 2 ^ 160 * Y) :
    128 * kapJ j * (1 / 2 ^ 60) * (|(w0 : ℝ)| + |(w1 : ℝ)|) ≤ Y := by
  have hp : ((p2 (sc + 100) : ℤ) : ℝ) = 2 ^ sc * 2 ^ 160 * (1 / 2 ^ 60) := by
    rw [p2_cast, pow_add, show (2 : ℝ) ^ 160 = 2 ^ 100 * 2 ^ 60 by norm_num]; field_simp
  push_cast [hp] at h
  have hpos : (0 : ℝ) < 2 ^ sc * 2 ^ 160 := by positivity
  rw [show (128 : ℝ) * (chartKI j : ℝ) * (|(w0 : ℝ)| + |(w1 : ℝ)|) * (2 ^ sc * 2 ^ 160 * (1 / 2 ^ 60)) =
    2 ^ sc * 2 ^ 160 * (128 * kapJ j * (1 / 2 ^ 60) * (|(w0 : ℝ)| + |(w1 : ℝ)|)) by
      simp only [kapJ]; ring] at h
  exact le_of_mul_le_mul_left h hpos

/-- The per-vertex hypothesis of `gap_core` at box point `t`. -/
def G1 (t : Fin 5 → ℝ) (tt : ℕ) : Prop :=
  128 * kapJ b.chart * (1 / 2 ^ 60) * (|(w0 : ℝ)| + |(w1 : ℝ)|) ≤
    cayleyDenom (kpt b t 1) (-kpt b t 0) 0 * kapJ b.chart *
      cayleyDenom (rOf (kblow b.chart) b.face (kpt b t) 0) (rOf (kblow b.chart) b.face (kpt b t) 1)
        (rOf (kblow b.chart) b.face (kpt b t) 2) *
      (lin w0 w1 ((outerRot (kpt b t 0) (kpt b t 1) * Qm b.chart (rOf (kblow b.chart) b.face (kpt b t)))
          *ᵥ vR s) - lin w0 w1 (outerRot (kpt b t 0) (kpt b t 1) *ᵥ vR tt))

/-- The paired hypothesis of `gap_core`. -/
def G2 (t : Fin 5 → ℝ) : Prop :=
  128 * kapJ b.chart * (1 / 2 ^ 60) * (|(w0 : ℝ)| + |(w1 : ℝ)|) ≤
    2 * lin w0 w1 (NoR (kpt b t) *ᵥ (chartMR b.chart *ᵥ
      (crossR (faceR b.face (kpt b t 2) (kpt b t 3)) (vR s) +
        kpt b t 4 • crossR (faceR b.face (kpt b t 2) (kpt b t 3))
          (crossR (faceR b.face (kpt b t 2) (kpt b t 3)) (vR s)))))

theorem G1_of (hj : b.chart < 5) (t : Fin 5 → ℝ) (tt : ℕ)
    (h : (gErr b w0 w1 : ℝ) ≤ (Fp b s w0 w1 (vt tt)).ev t) : G1 b s w0 w1 t tt := by
  rw [Fp_real b s w0 w1 hj t] at h
  exact err_scale w0 w1 b.chart h

theorem full_G1 (hj : b.chart < 5) (hf : b.face < 6) (hn : gapNrmOK b (vt s) w0 w1 = true)
    {tt : ℕ} (htt : tt < 90) (hfull : fullOK b (vt s) w0 w1 (vt tt).1 (vt tt).2.1 (vt tt).2.2 = true)
    {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) : G1 b s w0 w1 t tt := by
  apply G1_of b s w0 w1 hj t tt
  have hfit := (fits_all b s w0 w1 hj hf (vt tt)).2.2.2.2.1
  have hb := (nrm_all b s w0 w1 hn (vt tt) (vt_bound tt htt)).2.2.2.2.1
  have e := (ints b s w0 w1).2.2.2.2.2 (vt tt)
  unfold fullOK at hfull
  rw [Bool.or_eq_true] at hfull
  rcases hfull with hfull | hfull
  · have hl : ((pLower ((Fp b s w0 w1 (vt tt)).ev pXv) : ℤ) : ℝ) ≤ (Fp b s w0 w1 (vt tt)).ev t :=
      pLower_le hfit hb ht
    have hfull' : gErr b w0 w1 ≤
        pLower (gF (pGapData b (vt s) w0 w1) (vt tt).1 (vt tt).2.1 (vt tt).2.2) :=
      @of_decide_eq_true _ (Int.decLe _ _) hfull
    have : ((gErr b w0 w1 : ℤ) : ℝ) ≤ ((pLower ((Fp b s w0 w1 (vt tt)).ev pXv) : ℤ) : ℝ) := by
      rw [← e]; exact_mod_cast hfull'
    exact this.trans hl
  · have hr := (bern_room (nrm_all390 b s w0 w1 hn (vt tt) (vt_bound tt htt)).2.2.2.2.1).1
    rw [e] at hfull
    exact bernGE_le hfit hr hfull ht

theorem pair_G2 (hj : b.chart < 5) (hf : b.face < 6) (hbl : b.chart = 0 ∨ b.chart = 4)
    (hn : gapNrmOK b (vt s) w0 w1 = true) (hp : pairOK b (vt s) w0 w1 = true)
    {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) : G2 b s w0 w1 t := by
  have hfit := (fits_all b s w0 w1 hj hf (0, 0, 0)).2.2.2.2.2
  have hb := (nrm_all b s w0 w1 hn (0, 0, 0) (by decide)).2.2.2.2.2
  have e := (ints b s w0 w1).2.1
  unfold pairOK at hp
  rw [Bool.or_eq_true] at hp
  have h1 : ((gErrL b w0 w1 : ℤ) : ℝ) ≤ 2 * (Lp b s w0 w1).ev t := by
    rcases hp with hp | hp
    · have hl : ((pLower ((Lp b s w0 w1).ev pXv) : ℤ) : ℝ) ≤ (Lp b s w0 w1).ev t :=
        pLower_le hfit hb ht
      have hp' : gErrL b w0 w1 ≤ 2 * pLower (gL (pGapData b (vt s) w0 w1)) :=
        @of_decide_eq_true _ (Int.decLe _ _) hp
      have : ((gErrL b w0 w1 : ℤ) : ℝ) ≤ 2 * ((pLower ((Lp b s w0 w1).ev pXv) : ℤ) : ℝ) := by
        rw [← e]; exact_mod_cast hp'
      linarith
    · have hfit2 : L3.Fits (PE.mul (PE.c 2) (Lp b s w0 w1)) := fun i => by
        have := hfit i; simp only [PE.deg, zero_add]; exact this
      have hr := (bern_room (nrm_all390 b s w0 w1 hn (0, 0, 0) (by decide)).2.2.2.2.2).2
      have hn2 : (PE.mul (PE.c 2) (Lp b s w0 w1)).nrm = 2 * (Lp b s w0 w1).nrm := rfl
      have hev2 : (PE.mul (PE.c 2) (Lp b s w0 w1)).ev pXv = Int.mul 2 (gL (pGapData b (vt s) w0 w1)) := by
        rw [e]; rfl
      rw [← hev2] at hp
      have := bernGE_le hfit2 (by rw [hn2]; exact hr) hp ht
      simpa [PE.ev] using this
  rw [Lp_real b s w0 w1 hj hbl t] at h1
  exact err_scale w0 w1 b.chart h1












theorem Fp_split (T : ℤ × ℤ × ℤ) (t : Fin 5 → ℝ) :
    (Fp b s w0 w1 T).ev t = (Ap b s w0 w1).ev t - ((T.1 : ℝ) * (Ep0 b s w0 w1).ev t +
      (T.2.1 : ℝ) * (Ep1 b s w0 w1).ev t + (T.2.2 : ℝ) * (Ep2 b s w0 w1).ev t) := by
  simp only [Fp, xp, Ep0, Ep1, Ep2, PE.ev]; ring

theorem quick_G1 (hj : b.chart < 5) (hf : b.face < 6) (hn : gapNrmOK b (vt s) w0 w1 = true)
    {tt : ℕ} (htt : tt < 90)
    (hC : 0 ≤ p2 639 + quickQ b (vt s) w0 w1 - p2 170 *
      ((((quickE b (vt s) w0 w1).1.c0.natAbs : ℤ) + (quickE b (vt s) w0 w1).2.1.c0.natAbs +
        (quickE b (vt s) w0 w1).2.2.c0.natAbs) + (((quickE b (vt s) w0 w1).1.abs : ℤ) +
        (quickE b (vt s) w0 w1).2.1.abs + (quickE b (vt s) w0 w1).2.2.abs)))
    (hC2 : p2 639 + quickQ b (vt s) w0 w1 - p2 170 *
      ((((quickE b (vt s) w0 w1).1.c0.natAbs : ℤ) + (quickE b (vt s) w0 w1).2.1.c0.natAbs +
        (quickE b (vt s) w0 w1).2.2.c0.natAbs) + (((quickE b (vt s) w0 w1).1.abs : ℤ) +
        (quickE b (vt s) w0 w1).2.1.abs + (quickE b (vt s) w0 w1).2.2.abs)) +
      2 * p2 170 * ((((quickE b (vt s) w0 w1).1.c0.natAbs : ℤ) + (quickE b (vt s) w0 w1).2.1.c0.natAbs +
        (quickE b (vt s) w0 w1).2.2.c0.natAbs) + (((quickE b (vt s) w0 w1).1.abs : ℤ) +
        (quickE b (vt s) w0 w1).2.1.abs + (quickE b (vt s) w0 w1).2.2.abs)) < p2 640)
    (hb : (quickV (p2 639 + quickQ b (vt s) w0 w1 - p2 170 *
      ((((quickE b (vt s) w0 w1).1.c0.natAbs : ℤ) + (quickE b (vt s) w0 w1).2.1.c0.natAbs +
        (quickE b (vt s) w0 w1).2.2.c0.natAbs) + (((quickE b (vt s) w0 w1).1.abs : ℤ) +
        (quickE b (vt s) w0 w1).2.1.abs + (quickE b (vt s) w0 w1).2.2.abs)))
      (quickE b (vt s) w0 w1).1.c0 (quickE b (vt s) w0 w1).2.1.c0 (quickE b (vt s) w0 w1).2.2.c0
      (quickE b (vt s) w0 w1).1.abs (quickE b (vt s) w0 w1).2.1.abs
      (quickE b (vt s) w0 w1).2.2.abs).testBit (640 * tt + 639) = true)
    {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) : G1 b s w0 w1 t tt := by
  have hq := quick_bit _ _ _ _ _ _ _ hC hC2 htt hb
  obtain ⟨fA, fE0, fE1, fE2, -, -⟩ := fits_all b s w0 w1 hj hf (0, 0, 0)
  obtain ⟨nA, nE0, nE1, nE2, -, -⟩ := nrm_all b s w0 w1 hn (0, 0, 0) (by decide)
  obtain ⟨iA, -, i0, i1, i2, -⟩ := ints b s w0 w1
  have sA := (pStats_sound fA nA ht).1
  have s0 := (pStats_sound fE0 nE0 ht).2
  have s1 := (pStats_sound fE1 nE1 ht).2
  have s2 := (pStats_sound fE2 nE2 ht).2
  simp only [quickQ, quickE] at hq
  rw [iA, i0, i1, i2] at hq
  apply G1_of b s w0 w1 hj t tt
  rw [Fp_split]
  apply quick_real sA s0 s1 s2
  have hq' : ((0 : ℤ) : ℝ) ≤ ((_ : ℤ) : ℝ) := Int.cast_le.2 hq
  push_cast at hq'
  linarith

end leaf

/-! ## Unfolding the checker -/

theorem vtestG_sound (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) (s : ℕ) (w0 w1 : ℤ)
    (hn : gapNrmOK b (vt s) w0 w1 = true) {tt : ℕ} (htt : tt < 90)
    (h : vtestG b s (vt s) w0 w1 tt (vt tt).1 (vt tt).2.1 (vt tt).2.2 = true) {t : Fin 5 → ℝ}
    (ht : ∀ i, |t i| ≤ 1) :
    G1 b s w0 w1 t tt ∨ (gPair b s = some tt ∧ pairOK b (vt s) w0 w1 = true) := by
  unfold vtestG at h
  split_ifs at h with hp
  · rcases Bool.or_eq_true_iff.1 h with h1 | h1
    · exact Or.inr ⟨hp, h1⟩
    · exact Or.inl (full_G1 b s w0 w1 hj hf hn htt (Bool.and_eq_true_iff.1 h1).2 ht)
  · exact Or.inl (full_G1 b s w0 w1 hj hf hn htt h ht)

theorem vt_lt_BT {t : ℕ} (ht : t < 90) :
    |(vt t).1| < (BT : ℤ) ∧ |(vt t).2.1| < (BT : ℤ) ∧ |(vt t).2.2| < (BT : ℤ) := by
  obtain ⟨b1, b2, b3⟩ := vt_bound t ht
  have hB : (2 : ℕ) ^ 161 ≤ BT := by unfold BT; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> rw [← Int.natCast_natAbs] <;> exact_mod_cast lt_of_lt_of_le ‹_› hB

theorem slot_vals {t : ℕ} (ht : t < 90) :
    slot tpx t - ((2 ^ 170 : ℕ) : ℤ) = (vt t).1 ∧ slot tpy t - ((2 ^ 170 : ℕ) : ℤ) = (vt t).2.1 ∧
      slot tpz t - ((2 ^ 170 : ℕ) : ℤ) = (vt t).2.2 := by
  obtain ⟨b1, b2, b3⟩ := vt_lt_BT ht
  have hd : ∀ (f : ℕ → ℤ), (∀ j < 90, |f j| < (BT : ℤ)) →
      ∀ j < 90, (fun t => (f t + BT).toNat) j < 2 ^ 640 := by
    intro f hf j hj
    have := abs_lt.1 (hf j hj)
    have h2 : ((BT : ℕ) : ℤ) * 2 < ((2 ^ 640 : ℕ) : ℤ) := by
      have : BT * 2 < 2 ^ 640 := by
        unfold BT; rw [← pow_succ]; exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      exact_mod_cast this
    simp only; omega
  have hx := hd (fun t => (vt t).1) (fun j hj => (vt_lt_BT hj).1)
  have hy := hd (fun t => (vt t).2.1) (fun j hj => (vt_lt_BT hj).2.1)
  have hz := hd (fun t => (vt t).2.2) (fun j hj => (vt_lt_BT hj).2.2)
  rw [tpx_eq, tpy_eq, tpz_eq, slot_eq hx ht, slot_eq hy ht, slot_eq hz ht]
  have hBT : ((2 ^ 170 : ℕ) : ℤ) = BT := by simp [BT]
  rw [hBT]
  refine ⟨?_, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (by linarith [(abs_lt.1 b1).1])]; ring
  · rw [Int.toNat_of_nonneg (by linarith [(abs_lt.1 b2).1])]; ring
  · rw [Int.toNat_of_nonneg (by linarith [(abs_lt.1 b3).1])]; ring

theorem vS_eq {s : ℕ} (hs : s < 90) : vS s = vt s := by
  obtain ⟨h1, h2, h3⟩ := slot_vals hs
  simp only [vS, h1, h2, h3]

theorem vtxIdx_all {P : ℕ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → Bool} (h : vtxIdx.all P = true)
    {t : ℕ} (ht : t < 90) :
    P (t, vt t, (((vt t).1.natAbs : ℤ), ((vt t).2.1.natAbs : ℤ), ((vt t).2.2.natAbs : ℤ))) = true := by
  have hlen : vtxI.length = 90 := by decide +kernel
  rw [List.all_eq_true] at h
  apply h
  have hl : t < vtxIdx.length := by simp [vtxIdx, hlen, ht]
  have := List.getElem_mem hl
  convert this using 1
  simp [vtxIdx, vt, List.getD_eq_getElem?_getD, hlen, ht]

theorem pGapOK_vertex (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) {s : ℕ} {w0 w1 : ℤ}
    (h : pGapOK b s w0 w1 = true) :
    s < 90 ∧ (w0 ≠ 0 ∨ w1 ≠ 0) ∧ gapNrmOK b (vt s) w0 w1 = true ∧
      ∀ tt < 90, ∀ t : Fin 5 → ℝ, (∀ i, |t i| ≤ 1) →
      G1 b s w0 w1 t tt ∨ (gPair b s = some tt ∧ pairOK b (vt s) w0 w1 = true) := by
  unfold pGapOK at h
  split_ifs at h with hs
  rw [vS_eq hs] at h
  refine ⟨hs, ?_⟩
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hw, hn⟩, hrest⟩ := h
  have hn' : gapNrmOK b (vt s) w0 w1 = true := hn
  refine ⟨hw, hn', fun tt htt t ht => ?_⟩
  split_ifs at hrest with hpk
  · simp only [decide_eq_true_eq] at hpk
    obtain ⟨hC, hC2⟩ := hpk
    set V := (quickV (p2 639 + quickQ b (vt s) w0 w1 - p2 170 *
        ((((quickE b (vt s) w0 w1).1.c0.natAbs : ℤ) + (quickE b (vt s) w0 w1).2.1.c0.natAbs +
          (quickE b (vt s) w0 w1).2.2.c0.natAbs) + (((quickE b (vt s) w0 w1).1.abs : ℤ) +
          (quickE b (vt s) w0 w1).2.1.abs + (quickE b (vt s) w0 w1).2.2.abs)))
        (quickE b (vt s) w0 w1).1.c0 (quickE b (vt s) w0 w1).2.1.c0 (quickE b (vt s) w0 w1).2.2.c0
        (quickE b (vt s) w0 w1).1.abs (quickE b (vt s) w0 w1).2.1.abs
        (quickE b (vt s) w0 w1).2.2.abs) with hV
    by_cases hbit : V.testBit (640 * tt + 639) = true
    · exact Or.inl (quick_G1 b s w0 w1 hj hf hn' htt hC hC2 hbit ht)
    · have hf' : (Nat.xor signT (Nat.land V signT)).testBit (640 * tt + 639) = true := by
        rw [testBit_fails V htt]; simpa using hbit
      have hv := vtxSplit_sound _ 8 0 90 _ hrest tt htt hf'
      simp only [zero_add] at hv
      obtain ⟨sx, sy, sz⟩ := slot_vals htt
      rw [sx, sy, sz] at hv
      exact vtestG_sound b hj hf s w0 w1 hn' htt hv ht
  · have hv := vtxIdx_all hrest htt
    exact vtestG_sound b hj hf s w0 w1 hn' htt hv ht

/-- **Soundness of a kernel gap leaf.** -/
theorem pGapOK_sound (b : KBox) (hj : b.chart < 5) (hf : b.face < 6) {s : ℕ} {w0 w1 : ℤ}
    (h : pGapOK b s w0 w1 = true) {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1)
    (hpt : PtOK b.chart b.face (kpt b t)) :
    ¬ RupPair (outerRot (kpt b t 0) (kpt b t 1))
      (outerRot (kpt b t 0) (kpt b t 1) * Qm b.chart (rOf (kblow b.chart) b.face (kpt b t))) := by
  obtain ⟨hs, hw, hn, hv⟩ := pGapOK_vertex b hj hf h
  apply gap_core b.chart b.face hj (kpt b t) hpt s hs w0 w1 hw (vR s) (vR_err hs) vR
    (fun tt htt => vR_err htt)
  intro tt htt
  rcases hv tt htt t ht with h1 | ⟨hp, hpo⟩
  · exact Or.inl h1
  · have hbl : b.chart = 0 ∨ b.chart = 4 := by
      by_contra hc; simp [gPair, hc] at hp
    have hpr : pairOf b.chart s = some tt := by simpa [gPair, hbl, kPair] using hp
    exact Or.inr ⟨hbl, hpr, pair_G2 b s w0 w1 hj hf hbl hn hpo ht⟩

end Cayley.Pack

end
