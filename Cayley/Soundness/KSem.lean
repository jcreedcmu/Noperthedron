module

public import Cayley.Soundness.Approx
public import Cayley.Checker.KTree

@[expose] public section

/-!
# Semantics of kernel boxes, and the geometric core of a gap leaf

A point of a kernel box `b` at normalized coordinates `t ∈ [-1,1]⁵` is
`X = (c + h t) / 2^K`. `gap_core` turns two families of real inequalities (one per outer
vertex, and the blown-up paired test) into `¬ RupPair`.
-/

namespace Cayley

open Noperthedron Real
open scoped Matrix

/-- The blow-up direction on cube face . -/
def faceR (face : ℕ) (s0 s1 : ℝ) : Fin 3 → ℝ :=
  let sg : ℝ := if face % 2 = 0 then 1 else -1
  match face / 2 with
  | 0 => ![sg, s0, s1]
  | 1 => ![s1, sg, s0]
  | _ => ![s0, s1, sg]

/-- Charts 0 and 4 are blown up. -/
def kblow (chart : ℕ) : Bool := chart = 0 || chart = 4

/-- The Cayley vector of a box point. -/
def rOf (blowup : Bool) (face : ℕ) (X : Fin 5 → ℝ) : Fin 3 → ℝ :=
  if blowup then X 4 • faceR face (X 2) (X 3) else ![X 2, X 3, X 4]

/-- The real point of a kernel box at normalized coordinates . -/
noncomputable def kpt (b : K.KBox) (t : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  ((b.c.getD i 0 : ℝ) + (b.h.getD i 0 : ℝ) * t i) / 2 ^ b.K

/-- The pose-validity facts the leaf proofs need about a box point. -/
structure PtOK (chart face : ℕ) (X : Fin 5 → ℝ) : Prop where
  disk : X 0 ^ 2 + X 1 ^ 2 ≤ 1
  rb : ∀ i, |rOf (kblow chart) face X i| ≤ 2
  blow : kblow chart = true → 0 ≤ X 4 ∧ X 4 ≤ 2 ∧ |X 2| ≤ 1 ∧ |X 3| ≤ 1

/-- A box point that would be a reduced Rupert pose. -/
def Bad (chart face : ℕ) (X : Fin 5 → ℝ) : Prop :=
  Reduced (X 0) (X 1) chart (rOf (kblow chart) face X) ∧
    RupPair (outerRot (X 0) (X 1)) (outerRot (X 0) (X 1) * Qm chart (rOf (kblow chart) face X))

/-- The outer numerator at a box point. -/
noncomputable def NoR (X : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  cayleyNumeratorMatrix (X 1) (-X 0) 0

/-- The chart weights `κⱼ` and the integer chart matrices `Mⱼ = κⱼ Bⱼ`, as reals. -/
noncomputable def kapJ (j : ℕ) : ℝ := (K.chartKI j : ℝ)

noncomputable def chartMR (j : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := K.chartMI j
  !![(m00 : ℝ), m01, m02; m10, m11, m12; m20, m21, m22]

theorem chartMR_eq (j : ℕ) (hj : j < 5) : chartMR j = kapJ j • chartB j := by
  have hk : kapR ≠ 0 := by unfold kapR c3xR c3yR; norm_num
  interval_cases j
  all_goals (ext a b; fin_cases a <;> fin_cases b <;>
    simp [chartMR, kapJ, K.chartMI, K.chartKI, chartB, tauR, kappaTau, c3x, c3y, kapR, c3xR, c3yR] <;>
    try field_simp)
  all_goals norm_num

theorem kapJ_ge (j : ℕ) : 1 ≤ kapJ j := by
  unfold kapJ K.chartKI
  split
  · simp [kappaTau, c3x, c3y]
  · simp

/-! ## Real-number facts -/

theorem lin_smul (w0 w1 c : ℝ) (x : Fin 3 → ℝ) : lin w0 w1 (c • x) = c * lin w0 w1 x := by
  simp [lin]; ring

theorem lin_sub (w0 w1 : ℝ) (x y : Fin 3 → ℝ) : lin w0 w1 (x - y) = lin w0 w1 x - lin w0 w1 y := by
  simp [lin]; ring

/-- An orthogonal matrix moves each coordinate of an `ε`-small vector by at most `2ε`. -/
theorem abs_mulVec_le {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rᵀ * R = 1) {e : Fin 3 → ℝ} {ε : ℝ}
    (he : ∀ i, |e i| ≤ ε) (i : Fin 3) : |(R *ᵥ e) i| ≤ 2 * ε := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (he 0)
  have hnorm : (R *ᵥ e) ⬝ᵥ (R *ᵥ e) = e ⬝ᵥ e := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose, hR,
      Matrix.transpose_one, Matrix.one_mulVec]
  have hsq : ∀ j, e j ^ 2 ≤ ε ^ 2 := fun j => by
    have := he j; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hsum : (R *ᵥ e) i ^ 2 ≤ 3 * ε ^ 2 := by
    have h0 := hsq 0; have h1 := hsq 1; have h2 := hsq 2
    simp only [dotProduct, Fin.sum_univ_three] at hnorm
    fin_cases i <;> simp <;> nlinarith [sq_nonneg ((R *ᵥ e) 0), sq_nonneg ((R *ᵥ e) 1),
      sq_nonneg ((R *ᵥ e) 2)]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((R *ᵥ e) i - 2 * ε), sq_nonneg ((R *ᵥ e) i + 2 * ε)]

theorem abs_lin_mulVec_le {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rᵀ * R = 1) {e : Fin 3 → ℝ}
    {ε : ℝ} (he : ∀ i, |e i| ≤ ε) (w0 w1 : ℝ) :
    |lin w0 w1 (R *ᵥ e)| ≤ 2 * ε * (|w0| + |w1|) := by
  have h0 := abs_mulVec_le hR he 0
  have h1 := abs_mulVec_le hR he 1
  unfold lin
  calc |w0 * (R *ᵥ e) 0 + w1 * (R *ᵥ e) 1| ≤ |w0| * |(R *ᵥ e) 0| + |w1| * |(R *ᵥ e) 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |w0| * (2 * ε) + |w1| * (2 * ε) := by gcongr
    _ = _ := by ring

theorem gap_identity (w0 w1 : ℝ) (Ro B C : Matrix (Fin 3) (Fin 3) ℝ) (Do κ Dr : ℝ)
    (y z : Fin 3 → ℝ) :
    lin w0 w1 ((Do • Ro) *ᵥ ((κ • B * (Dr • C)) *ᵥ y)) - κ * Dr * lin w0 w1 ((Do • Ro) *ᵥ z) =
      Do * κ * Dr * (lin w0 w1 ((Ro * (B * C)) *ᵥ y) - lin w0 w1 (Ro *ᵥ z)) := by
  simp only [lin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul]
  ring

theorem num_sub_denom (r S : Fin 3 → ℝ) :
    cayleyNumeratorMatrix (r 0) (r 1) (r 2) *ᵥ S - cayleyDenom (r 0) (r 1) (r 2) • S =
      (2 : ℝ) • (crossR r S + crossR r (crossR r S)) := by
  ext i; fin_cases i <;>
    simp [cayleyNumeratorMatrix, cayleyDenom, crossR, dotProduct, Fin.sum_univ_three] <;> ring

theorem crossR_smul_left (c : ℝ) (a b : Fin 3 → ℝ) : crossR (c • a) b = c • crossR a b := by
  ext i; fin_cases i <;> simp [crossR] <;> ring

theorem faceR_bound (face : ℕ) (s0 s1 : ℝ) (h0 : |s0| ≤ 1) (h1 : |s1| ≤ 1) :
    ∀ i, |faceR face s0 s1 i| ≤ 1 := by
  intro i
  simp only [faceR]
  generalize face / 2 = m
  have hsg : |(if face % 2 = 0 then (1 : ℝ) else -1)| ≤ 1 := by split_ifs <;> simp
  rcases m with _ | _ | m <;> fin_cases i <;> simpa using ‹_›

theorem crossR_bound {c e : Fin 3 → ℝ} {δ : ℝ} (hc : ∀ i, |c i| ≤ 1) (he : ∀ i, |e i| ≤ δ) :
    ∀ i, |crossR c e i| ≤ 2 * δ := by
  have hp : ∀ a b, |c a * e b| ≤ δ := fun a b => by
    rw [abs_mul]
    calc |c a| * |e b| ≤ 1 * δ := mul_le_mul (hc a) (he b) (abs_nonneg _) (by norm_num)
      _ = δ := one_mul δ
  intro i
  fin_cases i <;> simp only [crossR] <;>
    · simp
      calc _ ≤ _ := abs_sub _ _
        _ ≤ δ + δ := add_le_add (hp _ _) (hp _ _)
        _ = 2 * δ := by ring

theorem crossR_sub (c x y : Fin 3 → ℝ) : crossR c (x - y) = crossR c x - crossR c y := by
  ext i; fin_cases i <;> simp [crossR] <;> ring

theorem crossR_smul_right (a : ℝ) (c x : Fin 3 → ℝ) : crossR c (a • x) = a • crossR c x := by
  ext i; fin_cases i <;> simp [crossR] <;> ring

theorem chartB_zero_mulVec (v : Fin 3 → ℝ) : chartB 0 *ᵥ v = v := by
  ext i; fin_cases i <;> simp [chartB, Matrix.mulVec, dotProduct, Fin.sum_univ_three]


/-! ## The geometric core of a gap leaf -/

theorem gap_core (chart face : ℕ) (hj : chart < 5) (X : Fin 5 → ℝ) (hpt : PtOK chart face X)
    (s : ℕ) (hs : s < 90) (w0 w1 : ℤ) (hw : w0 ≠ 0 ∨ w1 ≠ 0)
    (Ŝ : Fin 3 → ℝ) (hS : ∀ i, |(vtx s - Ŝ) i| ≤ 1 / 2 ^ 60)
    (Th : ℕ → Fin 3 → ℝ) (hT : ∀ tt < 90, ∀ i, |(vtx tt - Th tt) i| ≤ 1 / 2 ^ 60)
    (hv : ∀ tt < 90,
      128 * kapJ chart * (1 / 2 ^ 60) * (|(w0 : ℝ)| + |(w1 : ℝ)|) ≤
        cayleyDenom (X 1) (-X 0) 0 * kapJ chart *
          cayleyDenom (rOf (kblow chart) face X 0) (rOf (kblow chart) face X 1)
            (rOf (kblow chart) face X 2) *
          (lin w0 w1 ((outerRot (X 0) (X 1) * Qm chart (rOf (kblow chart) face X)) *ᵥ Ŝ) -
            lin w0 w1 (outerRot (X 0) (X 1) *ᵥ Th tt)) ∨
      ((chart = 0 ∨ chart = 4) ∧ pairOf chart s = some tt ∧
        128 * kapJ chart * (1 / 2 ^ 60) * (|(w0 : ℝ)| + |(w1 : ℝ)|) ≤
          2 * lin w0 w1 (NoR X *ᵥ (chartMR chart *ᵥ (crossR (faceR face (X 2) (X 3)) Ŝ +
            X 4 • crossR (faceR face (X 2) (X 3)) (crossR (faceR face (X 2) (X 3)) Ŝ)))))) :
    ¬ RupPair (outerRot (X 0) (X 1)) (outerRot (X 0) (X 1) * Qm chart (rOf (kblow chart) face X)) := by
  set r := rOf (kblow chart) face X
  set Ro := outerRot (X 0) (X 1)
  set Ri := Ro * Qm chart r
  set ε : ℝ := 1 / 2 ^ 60
  set κ := kapJ chart
  set Do := cayleyDenom (X 1) (-X 0) 0
  set Dr := cayleyDenom (r 0) (r 1) (r 2)
  set W := |(w0 : ℝ)| + |(w1 : ℝ)|
  have hε : 0 < ε := by positivity
  have hκ := kapJ_ge chart
  have hDo : 1 ≤ Do ∧ Do ≤ 2 := by
    simp only [Do, cayleyDenom]; constructor <;> nlinarith [hpt.disk, sq_nonneg (X 0), sq_nonneg (X 1)]
  have hDr : 1 ≤ Dr ∧ Dr ≤ 13 := by
    have h0 := hpt.rb 0; have h1 := hpt.rb 1; have h2 := hpt.rb 2
    rw [abs_le] at h0 h1 h2
    simp only [Dr, cayleyDenom]
    constructor <;> nlinarith [sq_nonneg (r 0), sq_nonneg (r 1), sq_nonneg (r 2)]
  have hRo : Roᵀ * Ro = 1 := SO3_transpose_mul (outerRot_mem_SO3 _ _)
  have hRiSO : Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (outerRot_mem_SO3 _ _)
      (Submonoid.mul_mem _ (chartB_mem_SO3 _) (cayV_mem_SO3 _))
  have hRi : Riᵀ * Ri = 1 := SO3_transpose_mul hRiSO
  have hw' : (w0 : ℝ) ≠ 0 ∨ (w1 : ℝ) ≠ 0 := by
    rcases hw with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have hW : 0 < W := by
    rcases hw' with h0 | h1
    · have := abs_pos.2 h0; positivity
    · have := abs_pos.2 h1; positivity
  apply not_rupPair_of_sep Ro Ri (vIdx s) w0 w1 hw'
  intro T
  obtain ⟨tt, htt, rfl⟩ := vIdx_surj T
  change lin w0 w1 (Ro *ᵥ vtx tt) ≤ lin w0 w1 (Ri *ᵥ vtx s)
  rcases hv tt htt with h1 | ⟨hbl, hpr, hL⟩
  swap
  · -- the paired vertex: blown-up chart, `vtx tt = B_j vtx s`
    have hbl' : kblow chart = true := by simp [kblow]; exact hbl
    have hσ : vtx tt = chartB chart *ᵥ vtx s := by
      unfold pairOf at hpr
      split_ifs at hpr with h0 h4
      · cases hpr; rw [h0, chartB_zero_mulVec]
      · rw [h4]; exact tau_pair s tt hs hpr
    obtain ⟨hρ0, hρ2, hs2, hs3⟩ := hpt.blow hbl'
    set c := faceR face (X 2) (X 3)
    set ρ := X 4
    set M := chartMR chart
    set B := chartB chart
    set Sv := vtx s
    have hc : ∀ i, |c i| ≤ 1 := faceR_bound _ _ _ hs2 hs3
    have hrc : r = ρ • c := by simp [r, rOf, hbl', c, ρ]
    have hM : M = κ • B := chartMR_eq _ hj
    have hNo : NoR X = Do • Ro := cayleyNumeratorMatrix_eq_denom_smul _ _ _
    set Lt := 2 * lin w0 w1 (NoR X *ᵥ (M *ᵥ (crossR c Sv + ρ • crossR c (crossR c Sv))))
    set Lh := 2 * lin w0 w1 (NoR X *ᵥ (M *ᵥ (crossR c Ŝ + ρ • crossR c (crossR c Ŝ))))
    have hRB : (Ro * B)ᵀ * (Ro * B) = 1 :=
      SO3_transpose_mul (Submonoid.mul_mem _ (outerRot_mem_SO3 _ _) (chartB_mem_SO3 _))
    have hdiff : |Lt - Lh| ≤ 80 * κ * ε * W := by
      set e := Sv - Ŝ
      set y := crossR c e + ρ • crossR c (crossR c e)
      have hy : ∀ i, |y i| ≤ 10 * ε := by
        have h1 := crossR_bound hc hS
        have h2 := crossR_bound hc h1
        intro i
        simp only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc |crossR c e i + ρ * crossR c (crossR c e) i|
            ≤ |crossR c e i| + |ρ| * |crossR c (crossR c e) i| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ 2 * ε + 2 * (2 * (2 * ε)) := by
              rw [abs_of_nonneg hρ0]
              gcongr
              · exact h1 i
              · exact h2 i
          _ ≤ 10 * ε := by linarith
      have hLd : Lt - Lh = 2 * (Do * κ) * lin w0 w1 ((Ro * B) *ᵥ y) := by
        simp only [Lt, Lh, y, e, crossR_sub, hNo, hM]
        simp only [lin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.smul_apply,
          Matrix.mul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        ring
      rw [hLd, abs_mul, abs_mul]
      have hl := abs_lin_mulVec_le hRB hy w0 w1
      have hDoκ : |Do * κ| ≤ 2 * κ := by
        rw [abs_of_nonneg (by have := hDo.1; positivity)]; nlinarith [hDo.2]
      calc |(2 : ℝ)| * |Do * κ| * |lin w0 w1 ((Ro * B) *ᵥ y)|
          ≤ 2 * (2 * κ) * (2 * (10 * ε) * W) := by
            rw [abs_two]; gcongr
        _ = 80 * κ * ε * W := by ring
    have hid : Do * κ * Dr * (lin w0 w1 (Ri *ᵥ Sv) - lin w0 w1 (Ro *ᵥ (B *ᵥ Sv))) = ρ * Lt := by
      have hNr := num_sub_denom r Sv
      have hC : cayleyNumeratorMatrix (r 0) (r 1) (r 2) = Dr • cayV r :=
        cayleyNumeratorMatrix_eq_denom_smul _ _ _
      rw [hrc, crossR_smul_left, crossR_smul_left, crossR_smul_right, ← hrc, hC] at hNr
      have h1 : Do * κ * Dr * lin w0 w1 (Ri *ᵥ Sv) =
          lin w0 w1 (NoR X *ᵥ (M *ᵥ ((Dr • cayV r) *ᵥ Sv))) := by
        rw [hNo, hM]
        simp only [Ri, Qm, Matrix.smul_mulVec, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, lin_smul]
        ring
      have h2 : Do * κ * Dr * lin w0 w1 (Ro *ᵥ (B *ᵥ Sv)) =
          lin w0 w1 (NoR X *ᵥ (M *ᵥ (Dr • Sv))) := by
        rw [hNo, hM]
        simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, lin_smul]
        ring
      rw [mul_sub, h1, h2, ← lin_sub, ← Matrix.mulVec_sub, ← Matrix.mulVec_sub, hNr]
      simp only [Lt, lin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    have hLt : 0 ≤ Lt := by
      have hεW : 0 ≤ ε * W := by positivity
      nlinarith [(abs_le.1 hdiff).1]
    have hG : 0 ≤ lin w0 w1 (Ri *ᵥ Sv) - lin w0 w1 (Ro *ᵥ (B *ᵥ Sv)) := by
      have hprod : 0 < Do * κ * Dr := by have := hDo.1; have := hDr.1; positivity
      have : 0 ≤ Do * κ * Dr * (lin w0 w1 (Ri *ᵥ Sv) - lin w0 w1 (Ro *ᵥ (B *ᵥ Sv))) := by
        rw [hid]; exact mul_nonneg hρ0 hLt
      exact nonneg_of_mul_nonneg_right this hprod
    rw [hσ]
    linarith
  · have hTt := hT tt htt
    -- the inner vertex barely moves
    have hinner : lin w0 w1 (Ri *ᵥ Ŝ) - 2 * ε * W ≤ lin w0 w1 (Ri *ᵥ vtx s) := by
      have := abs_lin_mulVec_le hRi hS w0 w1
      rw [Matrix.mulVec_sub, lin_sub] at this
      linarith [(abs_le.1 this).1]
    set Ĝ := lin w0 w1 (Ri *ᵥ Ŝ) - lin w0 w1 (Ro *ᵥ Th tt)
    have hprod : 0 < Do * κ * Dr := by
      have := hDo.1; have := hDr.1; positivity
    have hĜ : 4 * ε * W ≤ Ĝ := by
      by_contra hlt
      push Not at hlt
      have : Do * κ * Dr * Ĝ ≤ Do * κ * Dr * (4 * ε * W) :=
        mul_le_mul_of_nonneg_left hlt.le hprod.le
      have hb : Do * κ * Dr ≤ 26 * κ := by
        have := mul_le_mul hDo.2 hDr.2 (by linarith [hDr.1]) (by norm_num)
        nlinarith
      have hεW : 0 < ε * W := mul_pos hε hW
      nlinarith
    have houter : lin w0 w1 (Ro *ᵥ vtx tt) ≤ lin w0 w1 (Ro *ᵥ Th tt) + 2 * ε * W := by
      have := abs_lin_mulVec_le hRo hTt w0 w1
      rw [Matrix.mulVec_sub, lin_sub] at this
      linarith [(abs_le.1 this).2]
    linarith

end Cayley

end
