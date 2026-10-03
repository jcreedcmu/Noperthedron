module

public import Noperthedron.Nopert231.AtlasFundamentalPrune
public import Noperthedron.Nopert231.IcoGroup

@[expose] public section

/-!
# The icosahedral Dirichlet cell and its checked prune

A relative rotation R is in the icosahedral max-trace cell when no rotation
of I increases its trace on the right (nopert229/notes/S.md §2.3, reduction 1).
Every R has a right I-translate in the cell (`exists_mul_ico_inFundamentalDomain`),
and the cell lies in the fivefold one (`InIcoFundamentalDomain.toFivefold`),
so the fivefold machinery stays valid.

`AtlasIcoPrune.Box` rejects a box of Cayley coordinates by one of the 12
neighbors G_n (rotations by ±72° about the 5-fold axes): with R = chart ·
cayley(w), the trace advantage trace(R G_n) − trace R times the Cayley
denominator is the quadratic Σ_ij (G_n)_ji − δ_ij) Num_ij(w). The checked
quadratic uses the C++ search's rounded neighbors (`icoNeighborNum`, error
at most 10⁻¹² per entry, `neighbor_close`), and |Num_ij| ≤ 4 on the Cayley
ball, so `approximationError` = 36 · 10⁻¹² covers the rounding. This is
`exact5d::IcoPruneValid` in nopert229.
-/

namespace Noperthedron.Nopert231

open scoped Matrix

/-! ### The icosahedral cell -/

/-- No right rotation of I increases the trace. -/
def InIcoFundamentalDomain (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ g : IcoIndex, Matrix.trace (R * icoMatrix g) ≤ Matrix.trace R

theorem exists_mul_ico_inFundamentalDomain (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ h : IcoIndex, InIcoFundamentalDomain (R * icoMatrix h) := by
  obtain ⟨h, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun g : IcoIndex => Matrix.trace (R * icoMatrix g)) Finset.univ_nonempty
  refine ⟨h, fun g => ?_⟩
  obtain ⟨k, hk⟩ := exists_icoMatrix_mul h g
  rw [Matrix.mul_assoc, hk]
  exact hmax k (Finset.mem_univ _)

theorem exists_icoMatrix_eq_fivefoldMatrix (k : OrbitIndex) :
    ∃ g : IcoIndex, fivefoldMatrix k = icoMatrix g := by
  have hrz : fivefoldMatrix 1 = icoMatrix ⟨icoRzIndex, by decide⟩ := by
    rw [icoMatrix, ico_rz]
    simp [fivefoldMatrix]
  suffices h : ∀ n (hn : n < 5), ∃ g : IcoIndex, fivefoldMatrix ⟨n, hn⟩ = icoMatrix g from
    h k.val k.isLt
  intro n
  induction n with
  | zero => intro _; exact ⟨0, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨g, hg⟩ := ih (by omega)
    have hstep : fivefoldMatrix ⟨n + 1, hn⟩ = fivefoldMatrix 1 * fivefoldMatrix ⟨n, by omega⟩ := by
      rw [fivefoldMatrix_mul]
      congr 1
      ext
      simp [composeSymmetry]
      omega
    obtain ⟨k, hk⟩ := exists_icoMatrix_mul ⟨icoRzIndex, by decide⟩ g
    exact ⟨k, by rw [hstep, hrz, hg, hk]⟩

theorem InIcoFundamentalDomain.toFivefold {R : Matrix (Fin 3) (Fin 3) ℝ}
    (h : InIcoFundamentalDomain R) : InFivefoldFundamentalDomain R := by
  intro k
  obtain ⟨g, hg⟩ := exists_icoMatrix_eq_fivefoldMatrix k
  rw [hg]
  exact h g

namespace AtlasIcoPrune

open Noperthedron.Checker
open CayleyAtlas

/-- The group index of neighbor `n`. -/
def neighborIndex (n : Fin 12) : Nat := icoNeighborIndex.getD n.val 0

/-- The rounded neighbor, as the C++ search uses it. -/
def neighborQ (n : Fin 12) (i j : Fin 3) : ℚ :=
  (((icoNeighborNum.getD n.val []).getD (3 * i.val + j.val) 0 : Int) : ℚ) / 10 ^ 12

def neighborCheck : Bool :=
  (List.finRange 12).all fun n =>
    decide (neighborIndex n < 60) &&
      (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
        let e := (icoEntry (neighborIndex n)).entry i j
        decide (|IcoZ.lo e / 20 - neighborQ n i j| ≤ 1 / 10 ^ 12) &&
          decide (|IcoZ.hi e / 20 - neighborQ n i j| ≤ 1 / 10 ^ 12)

theorem neighborCheck_eq : neighborCheck = true := by decide +kernel

theorem neighborIndex_lt (n : Fin 12) : neighborIndex n < 60 := by
  have hc := neighborCheck_eq
  simp only [neighborCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq] at hc
  exact (hc n).1

/-- Neighbor `n` as a group element. -/
def neighbor (n : Fin 12) : IcoIndex := ⟨neighborIndex n, neighborIndex_lt n⟩

theorem neighbor_close (n : Fin 12) (i j : Fin 3) :
    |icoMatrix (neighbor n) i j - neighborQ n i j| ≤ 1 / 10 ^ 12 := by
  have hc := neighborCheck_eq
  simp only [neighborCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlo, hhi⟩ := (hc n).2 i j
  set e := (icoEntry (neighborIndex n)).entry i j
  have hval : icoMatrix (neighbor n) i j = IcoZ.val e / 20 := by
    simp [icoMatrix, ico, neighbor, M3.toMatrix, e]
    ring
  have h1 := IcoZ.lo_le_val e
  have h2 := IcoZ.val_le_hi e
  have hlo' : |((IcoZ.lo e / 20 - neighborQ n i j : ℚ) : ℝ)| ≤ ((1 / 10 ^ 12 : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    exact_mod_cast hlo
  have hhi' : |((IcoZ.hi e / 20 - neighborQ n i j : ℚ) : ℝ)| ≤ ((1 / 10 ^ 12 : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    exact_mod_cast hhi
  rw [abs_le] at hlo' hhi' ⊢
  push_cast at hlo' hhi' ⊢
  rw [hval]
  constructor <;> linarith [hlo'.1, hlo'.2, hhi'.1, hhi'.2]

/-- `Σ_ij (G~_n)_ji − δ_ij) Num_ij`: the denominator-cleared trace advantage
with the rounded neighbor. -/
def advantageQuadratic (chart : ChartIndex) (n : Fin 12) : RatQuadratic3 :=
  AtlasQuadratic.sum3Q fun i => AtlasQuadratic.sum3Q fun j =>
    RatQuadratic3.scale (neighborQ n j i - if i = j then 1 else 0)
      (AtlasQuadratic.numeratorQuadratic chart i j)

def approximationError : ℚ := 36 / 10 ^ 12

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  neighbor : Fin 12
deriving DecidableEq

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.tightLower (box : Box) : ℚ :=
  let ball := RatQuadratic3.evalTightBall box.variableBalls
    (advantageQuadratic box.chart box.neighbor)
  ball.center - ball.radius

def Box.lower (box : Box) : ℚ :=
  max box.tightLower
    (QuadraticBernstein.lower box.variableBalls
      (advantageQuadratic box.chart box.neighbor))

def Box.Valid (box : Box) : Prop := approximationError < box.lower

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

theorem Box.lower_le_eval (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    (box.lower : ℝ) ≤
      (advantageQuadratic box.chart box.neighbor).evalReal p.x p.y p.z := by
  have hvars : ∀ i : Fin 3,
      (box.variableBalls i).Holds (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  have htight := RatBall.lower_le_of_holds
    (RatQuadratic3.evalTightBall_holds hvars
      (advantageQuadratic box.chart box.neighbor))
  have hbernstein := QuadraticBernstein.lower_le_evalReal hvars
    (advantageQuadratic box.chart box.neighbor)
  push_cast at htight hbernstein
  unfold Box.lower Box.tightLower
  push_cast
  exact max_le htight hbernstein

/-- The exact denominator-cleared trace advantage of neighbor `n`. -/
noncomputable def exactAdvantage (chart : ChartIndex) (n : Fin 12) (x y z : ℝ) : ℝ :=
  ∑ i, ∑ j, (icoMatrix (neighbor n) j i - if i = j then 1 else 0) *
    (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z

theorem eval_numerator_eq (chart : ChartIndex) (i j : Fin 3) (x y z : ℝ) :
    (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z =
      cayleyDenom x y z * (chartMatrix chart * cayleyMatrix x y z) i j := by
  rw [AtlasQuadratic.eval_numeratorQuadratic, cayleyNumeratorMatrix_eq_denom_smul,
    Matrix.mul_smul]
  simp

theorem trace_advantage_eq (chart : ChartIndex) (n : Fin 12) (x y z : ℝ) :
    Matrix.trace ((chartMatrix chart * cayleyMatrix x y z) * icoMatrix (neighbor n)) -
        Matrix.trace (chartMatrix chart * cayleyMatrix x y z) =
      exactAdvantage chart n x y z / cayleyDenom x y z := by
  have hd := (cayleyDenom_pos x y z).ne'
  rw [eq_div_iff hd]
  simp only [exactAdvantage, eval_numerator_eq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_three]
  simp
  ring

/-- Entries of an orthogonal matrix are at most 1 in absolute value. -/
theorem abs_entry_le_one {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (i j : Fin 3) : |M i j| ≤ 1 := by
  have h := congrFun (congrFun ((Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM) j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq,
    Fin.sum_univ_three] at h
  rw [abs_le]
  fin_cases i <;> simp at h ⊢ <;> constructor <;>
    nlinarith [sq_nonneg (M 0 j), sq_nonneg (M 1 j), sq_nonneg (M 2 j)]

theorem abs_numerator_le_four (chart : ChartIndex) (i j : Fin 3) (x y z : ℝ)
    (hbounded : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) :
    |(AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z| ≤ 4 := by
  rw [eval_numerator_eq, abs_mul, abs_of_pos (cayleyDenom_pos x y z)]
  have hR : chartMatrix chart * cayleyMatrix x y z ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (chartMatrix_mem_SO3 chart).1 (cayleyMatrix_mem_SO3 x y z).1
  have he := abs_entry_le_one hR i j
  have hden : cayleyDenom x y z ≤ 4 := by unfold cayleyDenom; linarith
  have hpos := (cayleyDenom_pos x y z).le
  calc cayleyDenom x y z * |(chartMatrix chart * cayleyMatrix x y z) i j|
      ≤ 4 * 1 := mul_le_mul hden he (abs_nonneg _) (by norm_num)
    _ = 4 := by norm_num

theorem advantage_approximation_error (chart : ChartIndex) (n : Fin 12) (x y z : ℝ)
    (hbounded : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) :
    |exactAdvantage chart n x y z -
        (advantageQuadratic chart n).evalReal x y z| ≤ (approximationError : ℝ) := by
  have hterm : ∀ i j : Fin 3,
      |(icoMatrix (neighbor n) j i - neighborQ n j i) *
          (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z| ≤ 4 / 10 ^ 12 := by
    intro i j
    rw [abs_mul]
    calc _ ≤ (1 / 10 ^ 12) * 4 :=
          mul_le_mul (neighbor_close n j i) (abs_numerator_le_four chart i j x y z hbounded)
            (abs_nonneg _) (by norm_num)
      _ = 4 / 10 ^ 12 := by ring
  have hdiff : exactAdvantage chart n x y z - (advantageQuadratic chart n).evalReal x y z =
      ∑ i, ∑ j, (icoMatrix (neighbor n) j i - neighborQ n j i) *
        (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z := by
    simp only [exactAdvantage, advantageQuadratic, AtlasQuadratic.sum3Q,
      RatQuadratic3.evalReal_add, RatQuadratic3.evalReal_scale, Fin.sum_univ_three]
    push_cast
    ring
  rw [hdiff]
  calc _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, (icoMatrix (neighbor n) j i - neighborQ n j i) *
          (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |(icoMatrix (neighbor n) j i - neighborQ n j i) *
          (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (4 / 10 ^ 12 : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (approximationError : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num [approximationError]

theorem Box.valid_imp_not_inIcoFundamentalDomain
    (box : Box) (hvalid : box.Valid) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (hbounded : p.CayleyBounded) :
    ¬ InIcoFundamentalDomain (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) := by
  intro hfund
  have hlower := box.lower_le_eval hp
  have herr := advantage_approximation_error box.chart box.neighbor p.x p.y p.z hbounded
  have hvalidReal : (approximationError : ℝ) < (box.lower : ℝ) := by
    exact_mod_cast hvalid
  have hpositive : 0 < exactAdvantage box.chart box.neighbor p.x p.y p.z := by
    rw [abs_le] at herr
    linarith
  have htrace := trace_advantage_eq box.chart box.neighbor p.x p.y p.z
  have hle := hfund (AtlasIcoPrune.neighbor box.neighbor)
  have : 0 < exactAdvantage box.chart box.neighbor p.x p.y p.z / cayleyDenom p.x p.y p.z :=
    div_pos hpositive (cayleyDenom_pos _ _ _)
  linarith

end AtlasIcoPrune

end Noperthedron.Nopert231
