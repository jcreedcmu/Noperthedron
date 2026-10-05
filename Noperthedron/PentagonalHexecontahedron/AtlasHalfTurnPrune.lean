module

public import Noperthedron.PentagonalHexecontahedron.AtlasIcoPrune
public import Noperthedron.PentagonalHexecontahedron.IcoGroupRounded
public import Noperthedron.PentagonalHexecontahedron.HalfTurn

@[expose] public section

/-!
# The half-turn cell and its checked prune

For a centrally symmetric solid, a pose with outer view u and relative
rotation R is Rupert iff the one with H_u R g is (g ∈ I; `HalfTurn.lean`), so R
may be taken in the half-turn cell: trace(H_u R G_g) ≤ trace R for every g.

`AtlasHalfTurnPrune.Box` rejects a box of Cayley coordinates over a view
triangle (corners P_c, views p = Σ λ_c P_c with λ ≥ 0) by one element g: with
G the rounded G_g (`icoGroupNum`), the degree-2 Bernstein coefficients in λ of
(trace(H_p R G) − trace R) |p|² D(w) are the quadratics in w
  b_cd = Σ_ik N_ik [P_c,i (G P_d)_k + P_d,i (G P_c)_k − (P_c·P_d)(G_ki + δ_ik)]
(N = D · chart · cayley(w) the Cayley numerator), and the box is pruned when
every b_cd exceeds its rounding allowance 2·10⁻¹² (6|P_c|₁|P_d|₁ + 9|P_c·P_d|).
This is `exact5d::HalfTurnPruneValid` in the C++ search.
-/

namespace Noperthedron.PentagonalHexecontahedron

open Noperthedron.Atlas
open scoped Matrix

/-- The half-turn about the line through `u` (for u ≠ 0). -/
noncomputable def halfTurnMat (u : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => 2 * u i * u j / (∑ k, u k ^ 2) - if i = j then 1 else 0

/-- No element of I gives a larger trace after the half-turn about the view. -/
def InHalfTurnCell (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ g : IcoIndex, Matrix.trace (halfTurnMat u * R * icoMatrix g) ≤ Matrix.trace R

namespace AtlasHalfTurnPrune

open Noperthedron.Checker
open CayleyAtlas

/-- The rounded group element `g`, as the C++ search uses it. -/
def groupQ (g : IcoIndex) (i j : Fin 3) : ℚ :=
  (((icoGroupNum.getD g.val []).getD (3 * i.val + j.val) 0 : Int) : ℚ) / 10 ^ 12

def groupCheck : Bool :=
  (List.finRange 60).all fun g =>
    (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
      let e := (icoEntry g.val).entry i j
      decide (|IcoZ.lo e / 20 - groupQ g i j| ≤ 5 / 10 ^ 13) &&
        decide (|IcoZ.hi e / 20 - groupQ g i j| ≤ 5 / 10 ^ 13)

theorem groupCheck_eq : groupCheck = true := by decide +kernel

theorem group_close (g : IcoIndex) (i j : Fin 3) :
    |icoMatrix g i j - groupQ g i j| ≤ 5 / 10 ^ 13 := by
  have hc := groupCheck_eq
  simp only [groupCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlo, hhi⟩ := hc g i j
  set e := (icoEntry g.val).entry i j
  have hval : icoMatrix g i j = IcoZ.val e / 20 := by
    simp [icoMatrix, ico, M3.toMatrix, e]
    ring
  have h1 := IcoZ.lo_le_val e
  have h2 := IcoZ.val_le_hi e
  have hlo' : |((IcoZ.lo e / 20 - groupQ g i j : ℚ) : ℝ)| ≤ ((5 / 10 ^ 13 : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    exact_mod_cast hlo
  have hhi' : |((IcoZ.hi e / 20 - groupQ g i j : ℚ) : ℝ)| ≤ ((5 / 10 ^ 13 : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    exact_mod_cast hhi
  rw [abs_le] at hlo' hhi' ⊢
  push_cast at hlo' hhi' ⊢
  rw [hval]
  constructor <;> linarith [hlo'.1, hlo'.2, hhi'.1, hhi'.2]

abbrev Triangle := Fin 3 → Fin 3 → ℚ

/-- `(G P)_k` for the rounded G. -/
def gApply (g : IcoIndex) (P : Fin 3 → ℚ) (k : Fin 3) : ℚ := ∑ j, groupQ g k j * P j

def dotQ (P Q : Fin 3 → ℚ) : ℚ := ∑ i, P i * Q i

/-- The coefficient of N_ik in b_cd (rounded G). -/
def coeff (tri : Triangle) (g : IcoIndex) (c d : Fin 3) (i k : Fin 3) : ℚ :=
  tri c i * gApply g (tri d) k + tri d i * gApply g (tri c) k -
    dotQ (tri c) (tri d) * (groupQ g k i + if i = k then 1 else 0)

/-- b_cd as a quadratic in the Cayley coordinates. -/
def coefficientQuadratic (chart : ChartIndex) (tri : Triangle) (g : IcoIndex) (c d : Fin 3) :
    RatQuadratic3 :=
  AtlasQuadratic.sum3Q fun i => AtlasQuadratic.sum3Q fun k =>
    RatQuadratic3.scale (coeff tri g c d i k) (AtlasQuadratic.numeratorQuadratic chart i k)

def l1 (P : Fin 3 → ℚ) : ℚ := |P 0| + |P 1| + |P 2|

/-- The rounding allowance of b_cd. -/
def allowance (tri : Triangle) (c d : Fin 3) : ℚ :=
  2 / 10 ^ 12 * (6 * l1 (tri c) * l1 (tri d) + 9 * |dotQ (tri c) (tri d)|)

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  triangle : Triangle
  element : IcoIndex
deriving DecidableEq

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.lower (box : Box) (c d : Fin 3) : ℚ :=
  let q := coefficientQuadratic box.chart box.triangle box.element c d
  let ball := RatQuadratic3.evalTightBall box.variableBalls q
  max (ball.center - ball.radius) (QuadraticBernstein.lower box.variableBalls q)

/-- The pairs c ≤ d. -/
def pairs : List (Fin 3 × Fin 3) := [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]

def Box.Valid (box : Box) : Prop :=
  ∀ cd ∈ pairs, allowance box.triangle cd.1 cd.2 < box.lower cd.1 cd.2

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

theorem Box.lower_le_eval (box : Box) (c d : Fin 3) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    (box.lower c d : ℝ) ≤
      (coefficientQuadratic box.chart box.triangle box.element c d).evalReal p.x p.y p.z := by
  have hvars : ∀ i : Fin 3,
      (box.variableBalls i).Holds (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  set q := coefficientQuadratic box.chart box.triangle box.element c d
  have htight := RatBall.lower_le_of_holds (RatQuadratic3.evalTightBall_holds hvars q)
  have hbernstein := QuadraticBernstein.lower_le_evalReal hvars q
  push_cast at htight hbernstein
  unfold Box.lower
  push_cast
  exact max_le htight hbernstein

/-! ### Exact coefficients and the identity -/

/-- b_cd's coefficient of N_ik with the exact group element. -/
noncomputable def exactCoeff (tri : Triangle) (g : IcoIndex) (c d i k : Fin 3) : ℝ :=
  (tri c i : ℝ) * (∑ j, icoMatrix g k j * (tri d j : ℝ)) +
    (tri d i : ℝ) * (∑ j, icoMatrix g k j * (tri c j : ℝ)) -
    (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) * (icoMatrix g k i + if i = k then 1 else 0)

/-- The exact b_cd at Cayley coordinates (x, y, z). -/
noncomputable def exactB (chart : ChartIndex) (tri : Triangle) (g : IcoIndex) (c d : Fin 3)
    (x y z : ℝ) : ℝ :=
  ∑ i, ∑ k, exactCoeff tri g c d i k * (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z

/-- The view p = Σ λ_c P_c. -/
def viewOf (tri : Triangle) (lam : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => ∑ c, lam c * (tri c i : ℝ)

/-- The algebra behind `sum_exactB`, for arbitrary matrices. -/
theorem bernstein_identity (R G : Matrix (Fin 3) (Fin 3) ℝ) (P : Fin 3 → Fin 3 → ℝ)
    (lam : Fin 3 → ℝ) (D : ℝ) :
    ∑ c, ∑ d, lam c * lam d * ∑ i, ∑ k,
        (P c i * (∑ j, G k j * P d j) + P d i * (∑ j, G k j * P c j) -
          (∑ m, P c m * P d m) * (G k i + if i = k then 1 else 0)) * (D * R i k) =
      D * (2 * ∑ i, ∑ k, ∑ j, (∑ c, lam c * P c i) * R i k * G k j * (∑ c, lam c * P c j) -
        (∑ m, (∑ c, lam c * P c m) ^ 2) * (∑ i, ∑ k, R i k * G k i + ∑ i, R i i)) := by
  simp only [Fin.sum_univ_three, Fin.isValue]
  simp only [show (0 : Fin 3) = 0 from rfl, show (1 : Fin 3) = 1 from rfl, if_pos, if_neg,
    Fin.reduceEq, ite_true, ite_false]
  ring

theorem sum_exactB (chart : ChartIndex) (tri : Triangle) (g : IcoIndex) (lam : Fin 3 → ℝ)
    (x y z : ℝ) :
    ∑ c, ∑ d, lam c * lam d * exactB chart tri g c d x y z =
      cayleyDenom x y z * (2 * ∑ i, ∑ k, ∑ j, viewOf tri lam i *
          (chartMatrix chart * cayleyMatrix x y z) i k * icoMatrix g k j * viewOf tri lam j -
        (∑ m, viewOf tri lam m ^ 2) *
          (∑ i, ∑ k, (chartMatrix chart * cayleyMatrix x y z) i k * icoMatrix g k i +
            ∑ i, (chartMatrix chart * cayleyMatrix x y z) i i)) := by
  have h := bernstein_identity (chartMatrix chart * cayleyMatrix x y z) (icoMatrix g)
    (fun c i => (tri c i : ℝ)) lam (cayleyDenom x y z)
  simp only [exactB, exactCoeff, AtlasIcoPrune.eval_numerator_eq, viewOf]
  exact h

/-! ### The rounding error -/

theorem eval_coefficientQuadratic (chart : ChartIndex) (tri : Triangle) (g : IcoIndex) (c d : Fin 3)
    (x y z : ℝ) :
    (coefficientQuadratic chart tri g c d).evalReal x y z =
      ∑ i, ∑ k, (coeff tri g c d i k : ℝ) *
        (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z := by
  simp only [coefficientQuadratic, AtlasQuadratic.sum3Q, RatQuadratic3.evalReal_add,
    RatQuadratic3.evalReal_scale, Fin.sum_univ_three]

theorem abs_gApply_sub (tri : Triangle) (g : IcoIndex) (e k : Fin 3) :
    |(∑ j, icoMatrix g k j * (tri e j : ℝ)) - (gApply g (tri e) k : ℝ)| ≤
      5 / 10 ^ 13 * (l1 (tri e) : ℝ) := by
  have hsub : (∑ j, icoMatrix g k j * (tri e j : ℝ)) - (gApply g (tri e) k : ℝ) =
      ∑ j, (icoMatrix g k j - groupQ g k j) * (tri e j : ℝ) := by
    simp only [gApply, Fin.sum_univ_three]
    push_cast
    ring
  rw [hsub]
  calc _ ≤ ∑ j, |(icoMatrix g k j - groupQ g k j) * (tri e j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, 5 / 10 ^ 13 * |(tri e j : ℝ)| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (group_close g k j) (abs_nonneg _)
    _ = 5 / 10 ^ 13 * (l1 (tri e) : ℝ) := by
        simp only [l1, Fin.sum_univ_three]
        push_cast
        ring

theorem abs_coeff_sub (tri : Triangle) (g : IcoIndex) (c d i k : Fin 3) :
    |exactCoeff tri g c d i k - (coeff tri g c d i k : ℝ)| ≤
      5 / 10 ^ 13 * (|(tri c i : ℝ)| * l1 (tri d) + |(tri d i : ℝ)| * l1 (tri c) +
        |(dotQ (tri c) (tri d) : ℝ)|) := by
  have hdot : (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) = (dotQ (tri c) (tri d) : ℝ) := by
    simp [dotQ]
  have hsub : exactCoeff tri g c d i k - (coeff tri g c d i k : ℝ) =
      (tri c i : ℝ) * ((∑ j, icoMatrix g k j * (tri d j : ℝ)) - (gApply g (tri d) k : ℝ)) +
      (tri d i : ℝ) * ((∑ j, icoMatrix g k j * (tri c j : ℝ)) - (gApply g (tri c) k : ℝ)) -
      (dotQ (tri c) (tri d) : ℝ) * (icoMatrix g k i - groupQ g k i) := by
    simp only [exactCoeff, coeff, hdot]
    push_cast
    split_ifs <;> ring
  rw [hsub]
  have h1 := abs_gApply_sub tri g d k
  have h2 := abs_gApply_sub tri g c k
  have h3 := group_close g k i
  calc _ ≤ |(tri c i : ℝ) * ((∑ j, icoMatrix g k j * (tri d j : ℝ)) - (gApply g (tri d) k : ℝ))| +
          |(tri d i : ℝ) * ((∑ j, icoMatrix g k j * (tri c j : ℝ)) - (gApply g (tri c) k : ℝ))| +
          |(dotQ (tri c) (tri d) : ℝ) * (icoMatrix g k i - groupQ g k i)| := by
        have := abs_add_le ((tri c i : ℝ) * ((∑ j, icoMatrix g k j * (tri d j : ℝ)) -
          (gApply g (tri d) k : ℝ)) + (tri d i : ℝ) * ((∑ j, icoMatrix g k j * (tri c j : ℝ)) -
          (gApply g (tri c) k : ℝ))) (-((dotQ (tri c) (tri d) : ℝ) * (icoMatrix g k i - groupQ g k i)))
        have h' := abs_add_le ((tri c i : ℝ) * ((∑ j, icoMatrix g k j * (tri d j : ℝ)) -
          (gApply g (tri d) k : ℝ))) ((tri d i : ℝ) * ((∑ j, icoMatrix g k j * (tri c j : ℝ)) -
          (gApply g (tri c) k : ℝ)))
        rw [abs_neg] at this
        rw [sub_eq_add_neg]
        linarith
    _ ≤ |(tri c i : ℝ)| * (5 / 10 ^ 13 * l1 (tri d)) + |(tri d i : ℝ)| * (5 / 10 ^ 13 * l1 (tri c)) +
          |(dotQ (tri c) (tri d) : ℝ)| * (5 / 10 ^ 13) := by
        rw [abs_mul, abs_mul, abs_mul]
        gcongr
    _ = _ := by ring

theorem exactB_approximation (chart : ChartIndex) (tri : Triangle) (g : IcoIndex) (c d : Fin 3)
    (x y z : ℝ) (hbounded : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) :
    |exactB chart tri g c d x y z - (coefficientQuadratic chart tri g c d).evalReal x y z| ≤
      (allowance tri c d : ℝ) := by
  rw [eval_coefficientQuadratic]
  have hdiff : exactB chart tri g c d x y z -
      ∑ i, ∑ k, (coeff tri g c d i k : ℝ) * (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z =
      ∑ i, ∑ k, (exactCoeff tri g c d i k - (coeff tri g c d i k : ℝ)) *
        (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z := by
    simp only [exactB, Fin.sum_univ_three]
    ring
  rw [hdiff]
  have hterm : ∀ i k : Fin 3,
      |(exactCoeff tri g c d i k - (coeff tri g c d i k : ℝ)) *
          (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z| ≤
        4 * (5 / 10 ^ 13 * (|(tri c i : ℝ)| * l1 (tri d) + |(tri d i : ℝ)| * l1 (tri c) +
          |(dotQ (tri c) (tri d) : ℝ)|)) := by
    intro i k
    rw [abs_mul, mul_comm]
    exact mul_le_mul (AtlasIcoPrune.abs_numerator_le_four chart i k x y z hbounded)
      (abs_coeff_sub tri g c d i k) (abs_nonneg _) (by norm_num)
  calc _ ≤ ∑ i, |∑ k, (exactCoeff tri g c d i k - (coeff tri g c d i k : ℝ)) *
          (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ k, |(exactCoeff tri g c d i k - (coeff tri g c d i k : ℝ)) *
          (AtlasQuadratic.numeratorQuadratic chart i k).evalReal x y z| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ k : Fin 3, 4 * (5 / 10 ^ 13 * (|(tri c i : ℝ)| * l1 (tri d) +
          |(tri d i : ℝ)| * l1 (tri c) + |(dotQ (tri c) (tri d) : ℝ)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k
    _ = (allowance tri c d : ℝ) := by
        simp only [allowance, l1, Fin.sum_univ_three]
        push_cast
        ring

/-! ### Soundness -/

theorem exactB_symm (chart : ChartIndex) (tri : Triangle) (g : IcoIndex) (c d : Fin 3)
    (x y z : ℝ) : exactB chart tri g c d x y z = exactB chart tri g d c x y z := by
  simp only [exactB, exactCoeff]
  congr 1
  ext i
  congr 1
  ext k
  congr 1
  rw [show (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) = ∑ m, (tri d m : ℝ) * (tri c m : ℝ) from
    Finset.sum_congr rfl fun m _ => mul_comm _ _]
  ring

theorem trace_halfTurn_mul (u : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (halfTurnMat u * M) =
      2 * (∑ i, ∑ j, u i * M i j * u j) / (∑ k, u k ^ 2) - Matrix.trace M := by
  have h : ∀ i j : Fin 3, halfTurnMat u i j = 2 * u i * u j / (∑ k, u k ^ 2) - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j
    simp [halfTurnMat, Matrix.one_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, h, sub_mul, Finset.sum_sub_distrib]
  have h1 : ∀ i, ∑ j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * M j i = M i i := by
    intro i
    simp [Matrix.one_apply]
  simp only [h1]
  congr 1
  simp only [Fin.sum_univ_three]
  ring

theorem quad_pos (B : Fin 3 → Fin 3 → ℝ) (hB : ∀ c d, 0 < B c d) (lam : Fin 3 → ℝ)
    (hlam : ∀ c, 0 ≤ lam c) (hpos : 0 < ∑ c, lam c) :
    0 < ∑ c, ∑ d, lam c * lam d * B c d := by
  obtain ⟨c0, hc0⟩ : ∃ c, 0 < lam c := by
    by_contra h
    push_neg at h
    have : ∑ c, lam c ≤ 0 := Finset.sum_nonpos fun c _ => h c
    linarith
  have hnn : ∀ c d, 0 ≤ lam c * lam d * B c d :=
    fun c d => mul_nonneg (mul_nonneg (hlam c) (hlam d)) (hB c d).le
  calc (0 : ℝ) < lam c0 * lam c0 * B c0 c0 := mul_pos (mul_pos hc0 hc0) (hB c0 c0)
    _ ≤ ∑ d, lam c0 * lam d * B c0 d := Finset.single_le_sum (fun d _ => hnn c0 d) (Finset.mem_univ c0)
    _ ≤ ∑ c, ∑ d, lam c * lam d * B c d :=
        Finset.single_le_sum (f := fun c => ∑ d, lam c * lam d * B c d)
          (fun c _ => Finset.sum_nonneg fun d _ => hnn c d) (Finset.mem_univ c0)

theorem pairs_cover : ∀ c d : Fin 3, (c, d) ∈ pairs ∨ (d, c) ∈ pairs := by decide

/-- If the λ-form is positive, the half-turn about u increases the trace. -/
theorem not_inHalfTurnCell_of_pos (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (g : IcoIndex)
    (hinner : 0 < 2 * ∑ i, ∑ k, ∑ j, u i * R i k * icoMatrix g k j * u j -
      (∑ m, u m ^ 2) * (∑ i, ∑ k, R i k * icoMatrix g k i + ∑ i, R i i)) :
    ¬ InHalfTurnCell u R := by
  intro hcell
  have hnorm : 0 < ∑ m, u m ^ 2 := by
    rcases (Finset.sum_nonneg fun m (_ : m ∈ Finset.univ) => sq_nonneg (u m)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : ∀ m, u m = 0 := fun m =>
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (u m))).mp h.symm m (Finset.mem_univ _))
      simp [hz] at hinner
  have hcellg := hcell g
  rw [Matrix.mul_assoc, trace_halfTurn_mul] at hcellg
  have hRG : ∑ i, ∑ j, u i * (R * icoMatrix g) i j * u j =
      ∑ i, ∑ k, ∑ j, u i * R i k * icoMatrix g k j * u j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have htrRG : Matrix.trace (R * icoMatrix g) = ∑ i, ∑ k, R i k * icoMatrix g k i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have htrR : Matrix.trace R = ∑ i, R i i := by simp [Matrix.trace]
  rw [hRG, htrRG, htrR] at hcellg
  rw [div_sub' (ne_of_gt hnorm), div_le_iff₀ hnorm] at hcellg
  nlinarith [hcellg, hinner, hnorm]

/-- A valid box: for every view p = Σ λ_c P_c (λ ≥ 0, not all 0) and every
pose of the box, R is not in the half-turn cell. -/
theorem Box.valid_imp_not_inHalfTurnCell (box : Box) (hvalid : box.Valid) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (hbounded : p.CayleyBounded)
    (lam : Fin 3 → ℝ) (hlam : ∀ c, 0 ≤ lam c) (hpos : 0 < ∑ c, lam c) :
    ¬ InHalfTurnCell (viewOf box.triangle lam) (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) := by
  have hb : p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ 3 := hbounded
  have hle : ∀ cd ∈ pairs, 0 < exactB box.chart box.triangle box.element cd.1 cd.2 p.x p.y p.z := by
    intro cd hcd
    have hl := box.lower_le_eval cd.1 cd.2 hp
    have ha := exactB_approximation box.chart box.triangle box.element cd.1 cd.2 p.x p.y p.z hb
    have hv : (allowance box.triangle cd.1 cd.2 : ℝ) < (box.lower cd.1 cd.2 : ℝ) := by
      exact_mod_cast hvalid cd hcd
    rw [abs_le] at ha
    linarith
  have hB : ∀ c d : Fin 3, 0 < exactB box.chart box.triangle box.element c d p.x p.y p.z := by
    intro c d
    rcases pairs_cover c d with h | h
    · exact hle (c, d) h
    · rw [exactB_symm]
      exact hle (d, c) h
  have hsum := quad_pos _ hB lam hlam hpos
  rw [sum_exactB] at hsum
  apply not_inHalfTurnCell_of_pos _ _ box.element
  have hD := cayleyDenom_pos p.x p.y p.z
  by_contra h
  push_neg at h
  have := mul_le_mul_of_nonneg_left h hD.le
  linarith

end AtlasHalfTurnPrune

end Noperthedron.PentagonalHexecontahedron
