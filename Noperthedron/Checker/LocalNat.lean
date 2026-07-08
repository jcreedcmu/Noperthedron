import Noperthedron.Checker.Local
import Noperthedron.Vertices.PythonInt

/-!
# Integer core of the local `Bεℚ` check

`BεℚPy.checkN` recomputes exactly what `BεℚPy.check` computes, but with every
hot-loop quantity represented by an integer numerator over a statically known
power-of-10 scale (enabled by the fixed-point `sqrtApprox16`):

* trig values `round13 (sin/cos_psum …)` — numerators at scale `10¹³`,
  obtained directly as `⌊… * 10¹³⌋`;
* matrix entries — scale `10²⁶`;
* vertex coordinates — bare `ℤ` literals at scale `10¹⁶`
  (`pythonVertexNumCurried`);
* row dots `M₂·v` — scale `10⁴²`; their `round13`s via `Int` division by
  `10²⁹` (which floors, for positive divisors) — scale `10¹³`;
* `sqrtℚUp16` values — `Nat.sqrt` of scaled integers, scale `10¹⁶`; the
  pose-independent pair norms come from the integer literals
  `sqrtDvCurriedN`;
* `κℚ`, `√2⁺ = 142/100`, `√5⁺ = 224/100` — absorbed into the constants;
* the row-uniform `ε`, `δ`, `r` enter through their num/den pairs, and each
  comparison is cross-multiplied by the (positive, row-constant) denominator
  products.

No `Array` appears anywhere: under `decide +kernel`, `Array.ofFn` tables cost
per *access* (the push chain re-reduces), which is why the first draft of
this function was no faster than the ℚ check. Curried `![…]` literals walk a
few dozen `Fin.cons` cells instead, and every arithmetic step is a single GMP
operation.

The equality lemma `checkN_eq_check` (for `0 < ε`, `0 < r` — the only regime
`Row.ValidLocal` evaluates it in; the `Decidable` instance will fall back to
the ℚ check otherwise) and the instance rewiring land separately.
-/

namespace Noperthedron.Solution.BεℚPy

open Noperthedron RationalApprox

/-- Integer form of `sqrtℚUp16` on inputs `S/10²⁶`: for `S ≤ 0` both are `0`;
otherwise the inner `⌈(S/10²⁶)·10³²⌉ = S·10⁶` is exact. Output scale `10¹⁶`. -/
def sqrtNum26 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (S * 10 ^ 6).toNat + 1 : ℕ)

/-- Integer form of `sqrtℚUp16` on inputs `S/10⁵²`: the inner ceiling
`⌈S/10²⁰⌉` is `-((-S)/10²⁰)` (floor division). Output scale `10¹⁶`. -/
def sqrtNum52 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (-(-S / 10 ^ 20)).toNat + 1 : ℕ)

/-- Integer rendering of `BεℚPy.check` (see the module docstring). All the
`let`-bound quantities are integer numerators; comments give the scales. -/
def checkN (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε δ r : ℚ) : Bool :=
  -- trig numerators (scale 10¹³) — the `round13` numerators of `sinℚ`/`cosℚ`
  let stN : ℤ := ⌊sin_psum 13 p.θ₂ * 10 ^ 13⌋
  let ctN : ℤ := ⌊cos_psum 13 p.θ₂ * 10 ^ 13⌋
  let spN : ℤ := ⌊sin_psum 13 p.φ₂ * 10 ^ 13⌋
  let cpN : ℤ := ⌊cos_psum 13 p.φ₂ * 10 ^ 13⌋
  -- matrix entries (scale 10²⁶); m₀₂ = 0 is dropped
  let E00 := -stN * 10 ^ 13
  let E01 := ctN * 10 ^ 13
  let E10 := -(ctN * cpN)
  let E11 := -(stN * cpN)
  let E12 := spN * 10 ^ 13
  -- row-uniform rational data as num/den pairs
  let εn : ℤ := ε.num
  let εd : ℤ := ε.den
  let δn : ℤ := δ.num
  let δd : ℤ := δ.den
  let rn : ℤ := r.num
  let rd : ℤ := r.den
  -- Frobenius-norm bound F2 (scale 10¹⁶): f16 of the entry-square sum
  -- (scale 10⁵²), with the inner ⌈·/10²⁰⌉ as integer ceiling division
  let froN := E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12
  let F2N := sqrtNum52 froN
  -- row-constant scale denominators (all positive when 0 < ε, 0 < r)
  let Dd1 := 100 * εd * 10 ^ 16                 -- scale of denom1/denom2/cD
  let Dn := 50 * εd ^ 2 * 10 ^ 26               -- scale of numer
  let Db := 100 * δd * εd * rn                  -- scale of bound
  let boundN := (100 * δn * εd + 224 * εn * δd) * rd
  let cDN := 200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
  let etermC := εn * (142 * εd + 100 * εn)      -- eterm = etermC / (50·εd²)
  let cheapM := Db * Dd1 ^ 2 * 10 ^ 32          -- RHS multiplier, cheap test
  (List.finRange 3).all fun i =>
    let Qi_idx := Qi i
    let w0 := pythonVertexNumCurried Qi_idx.ℓ Qi_idx.i Qi_idx.k 0
    let w1 := pythonVertexNumCurried Qi_idx.ℓ Qi_idx.i Qi_idx.k 1
    let w2 := pythonVertexNumCurried Qi_idx.ℓ Qi_idx.i Qi_idx.k 2
    let mq0 := E00 * w0 + E01 * w1               -- scale 10⁴²
    let mq1 := E10 * w0 + E11 * w1 + E12 * w2
    let q0 := mq0 / 10 ^ 29                      -- scale 10¹³
    let q1 := mq1 / 10 ^ 29
    let s1 := sqrtNum26 (q0 * q0 + q1 * q1)
    let denom1N := 100 * εd * s1 + 142 * εn * 10 ^ 16 + 300 * εd * 10 ^ 6
    let bdN := boundN * denom1N
    decide <| ∀ k : VertexIndex, k ≠ Qi_idx →
      let v0 := pythonVertexNumCurried k.ℓ k.i k.k 0
      let v1 := pythonVertexNumCurried k.ℓ k.i k.k 1
      let v2 := pythonVertexNumCurried k.ℓ k.i k.k 2
      let d0 := (mq0 - (E00 * v0 + E01 * v1)) / 10 ^ 29               -- scale 10¹³
      let d1 := (mq1 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29
      let ndv := sqrtDvCurriedN Qi_idx.ℓ Qi_idx.i Qi_idx.k k.ℓ k.i k.k -- scale 10¹⁶
      let A := q0 * d0 + q1 * d1 - 10 ^ 17       -- scale 10²⁶
      let B := ndv + 2 * 10 ^ 6                  -- scale 10¹⁶
      let numerN := 50 * εd ^ 2 * A - etermC * B * 10 ^ 10
      (0 ≤ numerN ∧ 0 ≤ εn ∧
        bdN * (F2N * ndv * Dd1 + cDN * 10 ^ 32) * Dn < numerN * cheapM) ∨
        (let s2 := sqrtNum26 (d0 * d0 + d1 * d1)
         let denom2N := 100 * εd * s2 + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
         boundN * (Dn * (denom1N * denom2N)) < numerN * (Dd1 ^ 2 * Db))


/-! ## Soundness: value bridges between the ℚ and ℤ pipelines -/

section Bridges

/-- Cross-multiplication for integer-cast fractions with positive
denominators. -/
private lemma intCast_div_lt_div_iff {a b A B : ℤ} (hA : (0:ℤ) < A) (hB : (0:ℤ) < B) :
    (a : ℚ) / (A : ℚ) < (b : ℚ) / (B : ℚ) ↔ a * B < b * A := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hA) (by exact_mod_cast hB)]
  exact_mod_cast Iff.rfl

private lemma intCast_div_nonneg_iff {n D : ℤ} (hD : (0:ℤ) < D) :
    0 ≤ (n : ℚ) / (D : ℚ) ↔ 0 ≤ n := by
  rw [le_div_iff₀ (by exact_mod_cast hD : (0:ℚ) < (D:ℚ))]
  simp

/-- `round13` on a scale-`10⁴²` integer fraction is integer division by
`10²⁹` (at scale `10¹³`). -/
private lemma round13_intCast_div42 (m : ℤ) :
    RationalApprox.round13 ((m : ℚ) / 10 ^ 42) = ((m / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13 := by
  have h : ⌊(m : ℚ) / 10 ^ 42 * 10 ^ 13⌋ = m / 10 ^ 29 := by
    rw [show (m : ℚ) / 10 ^ 42 * 10 ^ 13 = (m : ℚ) / ((10 ^ 29 : ℕ) : ℚ) from by
      push_cast; ring]
    rw [Rat.floor_intCast_div_natCast]
    norm_num
  unfold RationalApprox.round13
  rw [h]

/-- `sqrtℚUp16` on a scale-`10²⁶` integer fraction is `sqrtNum26` (at scale
`10¹⁶`). -/
private lemma sqrtℚUp16_intCast_div26 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 26) = (sqrtNum26 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum26
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
        if_pos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 26 * 10 ^ 32⌉ = S * 10 ^ 6 := by
      rw [show (S : ℚ) / 10 ^ 26 * 10 ^ 32 = ((S * 10 ^ 6 : ℤ) : ℚ) from by
        push_cast; ring]
      exact Int.ceil_intCast _
    rw [hceil]
    push_cast
    ring

/-- `sqrtℚUp16` on a scale-`10⁵²` integer fraction is `sqrtNum52` (at scale
`10¹⁶`). -/
private lemma sqrtℚUp16_intCast_div52 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 52) = (sqrtNum52 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum52
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
        if_pos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 52 * 10 ^ 32⌉ = -(-S / 10 ^ 20) := by
      rw [show (S : ℚ) / 10 ^ 52 * 10 ^ 32 = -(((-S : ℤ) : ℚ) / ((10 ^ 20 : ℕ) : ℚ)) from by
        push_cast; ring]
      rw [Int.ceil_neg, Rat.floor_intCast_div_natCast]
      norm_num
    rw [hceil]
    push_cast
    ring

end Bridges

end Noperthedron.Solution.BεℚPy
