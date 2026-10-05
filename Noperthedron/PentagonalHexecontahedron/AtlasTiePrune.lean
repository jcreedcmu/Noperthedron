module

public import Noperthedron.PentagonalHexecontahedron.AtlasHalfTurnPrune
public import Noperthedron.PentagonalHexecontahedron.DHTieData

@[expose] public section

/-!
# The tie leaf's trace bound

A tie leaf of the 5D search (pack tag 15) claims that over its view triangle
(corners P_c, views p = Σ λ_c P_c, λ ≥ 0) and Cayley box, the rotation
S = H_p R H_x about the pinning normal x_n is within ρ of the identity:
trace(H_p R H_x) > τ(ρ) = (3 − ρ²)/(1 + ρ²). As for the half-turn prune
(`AtlasHalfTurnPrune`), with G the rounded H_x (`dhTieNum`), the degree-2
Bernstein coefficients in λ of (trace(H_p R G) − τ)|p|² D(w) are quadratics in w
  b_cd = Σ_ik N_ik [P_c,i (G P_d)_k + P_d,i (G P_c)_k − (P_c·P_d) G_ki] − τ (P_c·P_d) D(w),
and the box is valid when every b_cd exceeds the rounding allowance. This is
`exact5d::TieLeafValid` in the C++ search. The exact H_x is `dhTieH` (decided:
H (x·x) = 2 x xᵀ − (x·x) I over K, and the rounding is within 5·10⁻¹³).
-/

namespace Noperthedron.PentagonalHexecontahedron

open Noperthedron.Atlas
open scoped Matrix

namespace AtlasTiePrune

open Noperthedron.Checker
open CayleyAtlas
open AtlasHalfTurnPrune (Triangle dotQ l1 allowance pairs viewOf pairs_cover quad_pos trace_halfTurn_mul)
open Cap NPoly PVec

/-- The rounded half-turn of normal n. -/
def tieQ (n : ℕ) (i j : Fin 3) : ℚ :=
  (((Tie.dhTieNum.getD n []).getD (3 * i.val + j.val) 0 : Int) : ℚ) / 10 ^ 12

def tieHK (n : ℕ) (i j : Fin 3) : IcoQ := (Tie.dhTieH.getD n 0) i j
def tieXK (n : ℕ) : KVec := Tie.dhTieX.getD n 0

/-- The exact half-turn about x_n. -/
noncomputable def tieMat (n : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := halfTurnMat (kv (tieXK n))

/-- Decided: H (x·x) = 2 x xᵀ − (x·x) I, x·x > 0, and |H − G| ≤ 5·10⁻¹³ entrywise. -/
def tieCheck : Bool :=
  decide (Tie.dhTieX.size = Tie.dhTieH.size) && decide (Tie.dhTieX.size = Tie.dhTieNum.size) &&
  (List.range Tie.dhTieX.size).all fun n =>
    decide (0 < IcoQ.lo (kdot (tieXK n) (tieXK n))) &&
    (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
      decide (IcoQ.mul (tieHK n i j) (kdot (tieXK n) (tieXK n)) =
        IcoQ.sub (IcoQ.scale 2 (IcoQ.mul (tieXK n i) (tieXK n j)))
          (if i = j then kdot (tieXK n) (tieXK n) else IcoQ.zero)) &&
      decide (|IcoQ.lo (tieHK n i j) - tieQ n i j| ≤ 5 / 10 ^ 13) &&
      decide (|IcoQ.hi (tieHK n i j) - tieQ n i j| ≤ 5 / 10 ^ 13)

theorem tieCheck_eq : tieCheck = true := by decide +kernel

theorem tieMat_eq (n : ℕ) (hn : n < Tie.dhTieX.size) (i j : Fin 3) : tieMat n i j = (tieHK n i j).val := by
  have hc := tieCheck_eq
  simp only [tieCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_finRange, forall_const,
    decide_eq_true_eq] at hc
  obtain ⟨hx, he⟩ := hc.2 n hn
  have hxx : 0 < rdot (kv (tieXK n)) (kv (tieXK n)) := by rw [← val_kdot]; exact Cap.lo_val_lt hx
  have h := congrArg IcoQ.val (he i j).1.1
  rw [show IcoQ.mul = (· * ·) from rfl, show IcoQ.sub = (· - ·) from rfl] at h
  have hz : IcoQ.zero.val = 0 := by simp [IcoQ.val, IcoQ.zero]
  have hif : (if i = j then kdot (tieXK n) (tieXK n) else IcoQ.zero).val =
      if i = j then rdot (kv (tieXK n)) (kv (tieXK n)) else 0 := by
    split_ifs <;> simp [val_kdot, hz]
  simp only [IcoQ.val_mul, IcoQ.val_sub, IcoQ.val_scale, hif, val_kdot] at h
  push_cast at h
  have hs : ∑ k, kv (tieXK n) k ^ 2 = rdot (kv (tieXK n)) (kv (tieXK n)) := by
    simp [rdot, Fin.sum_univ_three, sq]
  simp only [tieMat, halfTurnMat]
  rw [hs]
  split_ifs at h ⊢ <;> simp only [kv, PVec.kval] at h hxx ⊢ <;> field_simp <;> linarith

theorem tie_close (n : ℕ) (hn : n < Tie.dhTieX.size) (i j : Fin 3) : |tieMat n i j - tieQ n i j| ≤ 5 / 10 ^ 13 := by
  have hc := tieCheck_eq
  simp only [tieCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_finRange, forall_const,
    decide_eq_true_eq] at hc
  obtain ⟨⟨-, hlo⟩, hhi⟩ := (hc.2 n hn).2 i j
  rw [tieMat_eq n hn]
  have h1 := IcoQ.lo_le_val (tieHK n i j)
  have h2 := IcoQ.val_le_hi (tieHK n i j)
  have hlo' : |((IcoQ.lo (tieHK n i j) - tieQ n i j : ℚ) : ℝ)| ≤ ((5 / 10 ^ 13 : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]; exact_mod_cast hlo
  have hhi' : |((IcoQ.hi (tieHK n i j) - tieQ n i j : ℚ) : ℝ)| ≤ ((5 / 10 ^ 13 : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]; exact_mod_cast hhi
  rw [abs_le] at hlo' hhi' ⊢
  push_cast at hlo' hhi' ⊢
  constructor <;> linarith [hlo'.1, hlo'.2, hhi'.1, hhi'.2]

/-- `(G P)_k` for the rounded G. -/
def gApply (n : ℕ) (P : Fin 3 → ℚ) (k : Fin 3) : ℚ := ∑ j, tieQ n k j * P j

/-- The coefficient of N_ik in b_cd (rounded G). -/
def coeff (tri : Triangle) (n : ℕ) (c d : Fin 3) (i k : Fin 3) : ℚ :=
  tri c i * gApply n (tri d) k + tri d i * gApply n (tri c) k - dotQ (tri c) (tri d) * tieQ n k i

def tau (ρ : ℚ) : ℚ := (3 - ρ ^ 2) / (1 + ρ ^ 2)

/-- b_cd as a quadratic in the Cayley coordinates. -/
def coefficientQuadratic (chart : ChartIndex) (tri : Triangle) (n : ℕ) (ρ : ℚ) (c d : Fin 3) :
    RatQuadratic3 :=
  AtlasQuadratic.sum3Q (fun i => AtlasQuadratic.sum3Q fun k =>
    RatQuadratic3.scale (coeff tri n c d i k) (AtlasQuadratic.numeratorQuadratic chart i k)) -
  RatQuadratic3.scale (tau ρ * dotQ (tri c) (tri d)) CayleyEdgeCertificate.denomQuadratic

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  triangle : Triangle
  normal : ℕ
  rho : ℚ
deriving DecidableEq

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2, box.interval.coordinateBall 3, box.interval.coordinateBall 4]

def Box.lower (box : Box) (c d : Fin 3) : ℚ :=
  let q := coefficientQuadratic box.chart box.triangle box.normal box.rho c d
  let ball := RatQuadratic3.evalTightBall box.variableBalls q
  max (ball.center - ball.radius) (QuadraticBernstein.lower box.variableBalls q)

def Box.Valid (box : Box) : Prop :=
  box.normal < Tie.dhTieX.size ∧ ∀ cd ∈ pairs, allowance box.triangle cd.1 cd.2 < box.lower cd.1 cd.2

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

theorem Box.lower_le_eval (box : Box) (c d : Fin 3) {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) :
    (box.lower c d : ℝ) ≤
      (coefficientQuadratic box.chart box.triangle box.normal box.rho c d).evalReal p.x p.y p.z := by
  have hvars : ∀ i : Fin 3, (box.variableBalls i).Holds (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  set q := coefficientQuadratic box.chart box.triangle box.normal box.rho c d
  have htight := RatBall.lower_le_of_holds (RatQuadratic3.evalTightBall_holds hvars q)
  have hbernstein := QuadraticBernstein.lower_le_evalReal hvars q
  push_cast at htight hbernstein
  unfold Box.lower
  push_cast
  exact max_le htight hbernstein

/-! ### Exact coefficients and the identity -/

noncomputable def exactCoeff (tri : Triangle) (n : ℕ) (c d i k : Fin 3) : ℝ :=
  (tri c i : ℝ) * (∑ j, tieMat n k j * (tri d j : ℝ)) +
    (tri d i : ℝ) * (∑ j, tieMat n k j * (tri c j : ℝ)) -
    (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) * tieMat n k i

noncomputable def exactB (chart : ChartIndex) (tri : Triangle) (n : ℕ) (ρ : ℚ) (c d : Fin 3) (x y z : ℝ) : ℝ :=
  ∑ i, ∑ k, exactCoeff tri n c d i k * (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z -
    (tau ρ : ℝ) * (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) * cayleyDenom x y z

theorem bernstein_identity (R G : Matrix (Fin 3) (Fin 3) ℝ) (P : Fin 3 → Fin 3 → ℝ)
    (lam : Fin 3 → ℝ) (D τ : ℝ) :
    ∑ c, ∑ d, lam c * lam d * (∑ i, ∑ k,
        (P c i * (∑ j, G k j * P d j) + P d i * (∑ j, G k j * P c j) -
          (∑ m, P c m * P d m) * G k i) * (D * R i k) - τ * (∑ m, P c m * P d m) * D) =
      D * (2 * ∑ i, ∑ k, ∑ j, (∑ c, lam c * P c i) * R i k * G k j * (∑ c, lam c * P c j) -
        (∑ m, (∑ c, lam c * P c m) ^ 2) * (∑ i, ∑ k, R i k * G k i + τ)) := by
  simp only [Fin.sum_univ_three, Fin.isValue]
  ring

theorem sum_exactB (chart : ChartIndex) (tri : Triangle) (n : ℕ) (ρ : ℚ) (lam : Fin 3 → ℝ) (x y z : ℝ) :
    ∑ c, ∑ d, lam c * lam d * exactB chart tri n ρ c d x y z =
      cayleyDenom x y z * (2 * ∑ i, ∑ k, ∑ j, viewOf tri lam i *
          (chartMatrix chart * cayleyMatrix x y z) i k * tieMat n k j * viewOf tri lam j -
        (∑ m, viewOf tri lam m ^ 2) *
          (∑ i, ∑ k, (chartMatrix chart * cayleyMatrix x y z) i k * tieMat n k i + (tau ρ : ℝ))) := by
  have h := bernstein_identity (chartMatrix chart * cayleyMatrix x y z) (tieMat n)
    (fun c i => (tri c i : ℝ)) lam (cayleyDenom x y z) (tau ρ)
  simp only [exactB, exactCoeff, AtlasIcoPrune.eval_numerator_eq, viewOf]
  exact h

/-! ### The rounding error -/

theorem eval_coefficientQuadratic (chart : ChartIndex) (tri : Triangle) (n : ℕ) (ρ : ℚ) (c d : Fin 3)
    (x y z : ℝ) :
    (coefficientQuadratic chart tri n ρ c d).evalReal x y z =
      ∑ i, ∑ k, (coeff tri n c d i k : ℝ) * (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z -
        ((tau ρ * dotQ (tri c) (tri d) : ℚ) : ℝ) * cayleyDenom x y z := by
  simp only [coefficientQuadratic, AtlasQuadratic.sum3Q, RatQuadratic3.evalReal_sub, RatQuadratic3.evalReal_add,
    RatQuadratic3.evalReal_scale, Fin.sum_univ_three, CayleyEdgeCertificate.eval_denomQuadratic]

theorem abs_gApply_sub (n : ℕ) (hn : n < Tie.dhTieX.size) (tri : Triangle) (e k : Fin 3) :
    |(∑ j, tieMat n k j * (tri e j : ℝ)) - (gApply n (tri e) k : ℝ)| ≤ 5 / 10 ^ 13 * (l1 (tri e) : ℝ) := by
  have hsub : (∑ j, tieMat n k j * (tri e j : ℝ)) - (gApply n (tri e) k : ℝ) =
      ∑ j, (tieMat n k j - tieQ n k j) * (tri e j : ℝ) := by
    simp only [gApply, Fin.sum_univ_three]
    push_cast
    ring
  rw [hsub]
  calc _ ≤ ∑ j, |(tieMat n k j - tieQ n k j) * (tri e j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, 5 / 10 ^ 13 * |(tri e j : ℝ)| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (tie_close n hn k j) (abs_nonneg _)
    _ = 5 / 10 ^ 13 * (l1 (tri e) : ℝ) := by
        simp only [l1, Fin.sum_univ_three]
        push_cast
        ring

theorem abs_coeff_sub (n : ℕ) (hn : n < Tie.dhTieX.size) (tri : Triangle) (c d i k : Fin 3) :
    |exactCoeff tri n c d i k - (coeff tri n c d i k : ℝ)| ≤
      5 / 10 ^ 13 * (|(tri c i : ℝ)| * l1 (tri d) + |(tri d i : ℝ)| * l1 (tri c) +
        |(dotQ (tri c) (tri d) : ℝ)|) := by
  have hdot : (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) = (dotQ (tri c) (tri d) : ℝ) := by
    simp [dotQ]
  have hsub : exactCoeff tri n c d i k - (coeff tri n c d i k : ℝ) =
      (tri c i : ℝ) * ((∑ j, tieMat n k j * (tri d j : ℝ)) - (gApply n (tri d) k : ℝ)) +
      (tri d i : ℝ) * ((∑ j, tieMat n k j * (tri c j : ℝ)) - (gApply n (tri c) k : ℝ)) -
      (dotQ (tri c) (tri d) : ℝ) * (tieMat n k i - tieQ n k i) := by
    simp only [exactCoeff, coeff, hdot]
    push_cast
    ring
  rw [hsub]
  have h1 := abs_gApply_sub n hn tri d k
  have h2 := abs_gApply_sub n hn tri c k
  have h3 := tie_close n hn k i
  set A := (tri c i : ℝ) * ((∑ j, tieMat n k j * (tri d j : ℝ)) - (gApply n (tri d) k : ℝ))
  set B := (tri d i : ℝ) * ((∑ j, tieMat n k j * (tri c j : ℝ)) - (gApply n (tri c) k : ℝ))
  set C := (dotQ (tri c) (tri d) : ℝ) * (tieMat n k i - tieQ n k i)
  have hA : |A| ≤ |(tri c i : ℝ)| * (5 / 10 ^ 13 * l1 (tri d)) := by
    simp only [A]; rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hB : |B| ≤ |(tri d i : ℝ)| * (5 / 10 ^ 13 * l1 (tri c)) := by
    simp only [B]; rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hC : |C| ≤ |(dotQ (tri c) (tri d) : ℝ)| * (5 / 10 ^ 13) := by
    simp only [C]; rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  calc |A + B - C| ≤ |A| + |B| + |C| := by
        have := abs_add_le (A + B) (-C)
        have := abs_add_le A B
        rw [abs_neg] at *
        rw [sub_eq_add_neg]
        linarith
    _ ≤ _ := by nlinarith [hA, hB, hC]

theorem exactB_approximation (n : ℕ) (hn : n < Tie.dhTieX.size) (chart : ChartIndex) (tri : Triangle) (ρ : ℚ)
    (c d : Fin 3) (x y z : ℝ) (hbounded : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) :
    |exactB chart tri n ρ c d x y z - (coefficientQuadratic chart tri n ρ c d).evalReal x y z| ≤
      (allowance tri c d : ℝ) := by
  rw [eval_coefficientQuadratic]
  have hdot : (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) = (dotQ (tri c) (tri d) : ℝ) := by simp [dotQ]
  have hdiff : exactB chart tri n ρ c d x y z -
      (∑ i, ∑ k, (coeff tri n c d i k : ℝ) * (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z -
        ((tau ρ * dotQ (tri c) (tri d) : ℚ) : ℝ) * cayleyDenom x y z) =
      ∑ i, ∑ k, (exactCoeff tri n c d i k - (coeff tri n c d i k : ℝ)) *
        (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z := by
    simp only [exactB, hdot, Fin.sum_univ_three]
    push_cast
    ring
  rw [hdiff]
  have hterm : ∀ i k : Fin 3,
      |(exactCoeff tri n c d i k - (coeff tri n c d i k : ℝ)) *
          (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z| ≤
        4 * (5 / 10 ^ 13 * (|(tri c i : ℝ)| * l1 (tri d) + |(tri d i : ℝ)| * l1 (tri c) +
          |(dotQ (tri c) (tri d) : ℝ)|)) := by
    intro i k
    rw [abs_mul, mul_comm]
    exact mul_le_mul (AtlasIcoPrune.abs_numerator_le_four chart i k x y z hbounded)
      (abs_coeff_sub n hn tri c d i k) (abs_nonneg _) (by norm_num)
  calc _ ≤ ∑ i, |∑ k, (exactCoeff tri n c d i k - (coeff tri n c d i k : ℝ)) *
          (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ k, |(exactCoeff tri n c d i k - (coeff tri n c d i k : ℝ)) *
          (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ k : Fin 3, 4 * (5 / 10 ^ 13 * (|(tri c i : ℝ)| * l1 (tri d) +
          |(tri d i : ℝ)| * l1 (tri c) + |(dotQ (tri c) (tri d) : ℝ)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k
    _ ≤ (allowance tri c d : ℝ) := by
        simp only [allowance, l1, Fin.sum_univ_three]
        push_cast
        have h0 := abs_nonneg ((dotQ (tri c) (tri d) : ℚ) : ℝ)
        have : ∀ e : Fin 3, 0 ≤ |((tri e 0 : ℚ) : ℝ)| + |((tri e 1 : ℚ) : ℝ)| + |((tri e 2 : ℚ) : ℝ)| :=
          fun e => by positivity
        nlinarith [this c, this d, abs_nonneg ((tri c 0 : ℚ) : ℝ), abs_nonneg ((tri c 1 : ℚ) : ℝ),
          abs_nonneg ((tri c 2 : ℚ) : ℝ), abs_nonneg ((tri d 0 : ℚ) : ℝ), abs_nonneg ((tri d 1 : ℚ) : ℝ),
          abs_nonneg ((tri d 2 : ℚ) : ℝ)]

/-! ### Soundness -/

theorem exactB_symm (chart : ChartIndex) (tri : Triangle) (n : ℕ) (ρ : ℚ) (c d : Fin 3) (x y z : ℝ) :
    exactB chart tri n ρ c d x y z = exactB chart tri n ρ d c x y z := by
  simp only [exactB, exactCoeff]
  rw [show (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) = ∑ m, (tri d m : ℝ) * (tri c m : ℝ) from
    Finset.sum_congr rfl fun m _ => mul_comm _ _]
  congr 1
  congr 1
  ext i
  congr 1
  ext k
  congr 1
  ring

/-- A positive λ-form gives trace(H_u R G) > τ. -/
theorem trace_gt_of_pos (u : Fin 3 → ℝ) (R G : Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (hinner : 0 < 2 * ∑ i, ∑ k, ∑ j, u i * R i k * G k j * u j -
      (∑ m, u m ^ 2) * (∑ i, ∑ k, R i k * G k i + τ)) :
    τ < Matrix.trace (halfTurnMat u * R * G) := by
  have hnorm : 0 < ∑ m, u m ^ 2 := by
    rcases (Finset.sum_nonneg fun m (_ : m ∈ Finset.univ) => sq_nonneg (u m)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : ∀ m, u m = 0 := fun m =>
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (u m))).mp h.symm m (Finset.mem_univ _))
      simp [hz] at hinner
  rw [Matrix.mul_assoc, trace_halfTurn_mul]
  have hRG : ∑ i, ∑ j, u i * (R * G) i j * u j = ∑ i, ∑ k, ∑ j, u i * R i k * G k j * u j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have htrRG : Matrix.trace (R * G) = ∑ i, ∑ k, R i k * G k i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [hRG, htrRG, lt_sub_iff_add_lt, lt_div_iff₀ hnorm]
  nlinarith [hinner, hnorm]

/-- A valid box: for every view p = Σ λ_c P_c (λ ≥ 0, not all 0) and every pose of the box,
trace(H_p R H_x) > τ(ρ). -/
theorem Box.valid_imp_trace (box : Box) (hvalid : box.Valid) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (hbounded : p.CayleyBounded)
    (lam : Fin 3 → ℝ) (hlam : ∀ c, 0 ≤ lam c) (hpos : 0 < ∑ c, lam c) :
    (tau box.rho : ℝ) < Matrix.trace (halfTurnMat (viewOf box.triangle lam) *
      (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) * tieMat box.normal) := by
  have hb : p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ 3 := hbounded
  obtain ⟨hn, hv⟩ := hvalid
  have hle : ∀ cd ∈ pairs, 0 < exactB box.chart box.triangle box.normal box.rho cd.1 cd.2 p.x p.y p.z := by
    intro cd hcd
    have hl := box.lower_le_eval cd.1 cd.2 hp
    have ha := exactB_approximation box.normal hn box.chart box.triangle box.rho cd.1 cd.2 p.x p.y p.z hb
    have hv' : (allowance box.triangle cd.1 cd.2 : ℝ) < (box.lower cd.1 cd.2 : ℝ) := by
      exact_mod_cast hv cd hcd
    rw [abs_le] at ha
    linarith
  have hB : ∀ c d : Fin 3, 0 < exactB box.chart box.triangle box.normal box.rho c d p.x p.y p.z := by
    intro c d
    rcases pairs_cover c d with h | h
    · exact hle (c, d) h
    · rw [exactB_symm]
      exact hle (d, c) h
  have hsum := quad_pos _ hB lam hlam hpos
  rw [sum_exactB] at hsum
  apply trace_gt_of_pos
  have hD := cayleyDenom_pos p.x p.y p.z
  by_contra h
  push Not at h
  have := mul_le_mul_of_nonneg_left h hD.le
  linarith

end AtlasTiePrune

end Noperthedron.PentagonalHexecontahedron
