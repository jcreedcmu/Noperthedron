module

public import Noperthedron.Checker.Local2NatOffset

@[expose] public section

/-!
# Integer rendering of `Row.δ₂` (kernel)

`Row.δ₂` is defined through the ℚ budget formulas (`ΔrotRMℚ`/`ΔrotMℚ`,
matrix norms, `Finset.max'`), and evaluating it under the kernel costs
~0.4s per second-order local row — a third of the remaining per-row time
after the offset tier.  This module renders the *exact* value as an
unreduced integer fraction `Row.δ₂PairZ : ℤ × ℤ`, computed from the same
`app6N` applied families the `Bε₂` core already evaluates (so the kernel's
term cache shares them), plus one `sqrtNum110` for the scale-`10¹¹⁰` head
atom and a three-variable analogue `budRM3` of `budN` for the `ΔrotRMℚ`
polynomial.

`Row.δ₂PairZ_eq` proves `Row.δ₂ = num / den` with `0 < den`, and the final
`Row.ValidLocal₂` instance (priority 10800) substitutes the fraction into
the `Bε₂ℚ` conjunct before deciding, so the ℚ definition is never
evaluated: the only ℚ-normalization left is the single division that
produces the fraction's `Rat` value.

The correctness proof converts whole applied families with `app6_intCast`,
then composes the displacement identity and the two budget bridges.
Coordinate casts and norm-atom scaling are proved once in `Local2Nat`.
-/

namespace Noperthedron.Solution.Local2Nat

open scoped Matrix

open RationalApprox (sinNum13 cosNum13 sinℚ cosℚ κℚ ΔrotMℚ ΔrotRMℚ ΔrotMℚs
  sqrtApprox16 UpperSqrt)
open Noperthedron.Solution.Local2Fast (App6 app6 fam2 norm2_eq app6_a0 app6_a1
  app6_b0 app6_b1 app6_c0 app6_c1 app6_d0 app6_d1 app6_e0 app6_e1 app6_f0
  app6_f1 dRotMs dRotMs_eq)

/-! ## Scale-`10¹¹⁰` upper square root -/

/-- `sqrtℚUp16` numerator for inputs at scale `10¹¹⁰`. -/
def sqrtNum110 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (-(-S / 10 ^ 78)).toNat + 1 : ℕ)

lemma sqrtℚUp16_intCast_div110 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 110) = (sqrtNum110 S : ℚ) / 10 ^ 16 := by
  convert sqrtℚUp16_intCast_div_scaled S (10 ^ 78) (by positivity) using 1 <;>
    norm_num [sqrtNum110]

/-! ## Three-variable ε-budget polynomial (`ΔrotRMℚ` shape) -/

/-- Cross-multiplied form (by `6·(ad·td·fd)³·10^s`) of the `ΔrotRMℚ` budget
`εα·a0 + εθ·a1 + εφ·a2 + ½(εα²a0 + 2εαεθ a1 + 2εαεφ a2 + εθ²a3 + 2εθεφ a4
+ εφ²a5) + rem·(εα+εθ+εφ)³/6` with atoms at scale `10^s`. -/
def budRM3 (a0 a1 a2 a3 a4 a5 rem an ad tn td fn fd : ℤ) : ℤ :=
  6 * an * ad ^ 2 * (td * fd) ^ 3 * a0
    + 6 * tn * td ^ 2 * (ad * fd) ^ 3 * a1
    + 6 * fn * fd ^ 2 * (ad * td) ^ 3 * a2
    + 3 * an ^ 2 * ad * (td * fd) ^ 3 * a0
    + 6 * an * tn * ad ^ 2 * td ^ 2 * fd ^ 3 * a1
    + 6 * an * fn * ad ^ 2 * fd ^ 2 * td ^ 3 * a2
    + 3 * tn ^ 2 * td * (ad * fd) ^ 3 * a3
    + 6 * tn * fn * td ^ 2 * fd ^ 2 * ad ^ 3 * a4
    + 3 * fn ^ 2 * fd * (ad * td) ^ 3 * a5
    + (an * td * fd + tn * ad * fd + fn * ad * td) ^ 3 * rem

/-- Value bridge for `budRM3`, over independent numerator/denominator data. -/
private lemma budRM3_div_eq' (a0N a1N a2N a3N a4N a5N remN u n m : ℤ) (c d e : ℕ)
    {a0 a1 a2 a3 a4 a5 rem εα εθ εφ : ℚ} (s : ℕ)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hα : εα = (u : ℚ) / (c : ℚ)) (hθ : εθ = (n : ℚ) / (d : ℚ))
    (hφ : εφ = (m : ℚ) / (e : ℚ))
    (h0 : a0 = (a0N : ℚ) / 10 ^ s) (h1 : a1 = (a1N : ℚ) / 10 ^ s)
    (h2 : a2 = (a2N : ℚ) / 10 ^ s) (h3 : a3 = (a3N : ℚ) / 10 ^ s)
    (h4 : a4 = (a4N : ℚ) / 10 ^ s) (h5 : a5 = (a5N : ℚ) / 10 ^ s)
    (hrem : rem = (remN : ℚ) / 10 ^ s) :
    εα * a0 + εθ * a1 + εφ * a2
        + (1/2) * (εα ^ 2 * a0 + 2 * (εα * εθ) * a1 + 2 * (εα * εφ) * a2
          + εθ ^ 2 * a3 + 2 * (εθ * εφ) * a4 + εφ ^ 2 * a5)
        + rem * (εα + εθ + εφ) ^ 3 / 6
      = ((budRM3 a0N a1N a2N a3N a4N a5N remN u c n d m e : ℤ) : ℚ)
        / (6 * ((c : ℚ) * (d : ℚ) * (e : ℚ)) ^ 3 * 10 ^ s) := by
  have hcQ : ((c : ℚ)) ≠ 0 := by exact_mod_cast hc
  have hdQ : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
  have heQ : ((e : ℚ)) ≠ 0 := by exact_mod_cast he
  have h10 : ((10 : ℚ)) ^ s ≠ 0 := by positivity
  rw [h0, h1, h2, h3, h4, h5, hrem, hα, hθ, hφ]
  unfold budRM3
  push_cast
  field_simp
  ring

/-- Value bridge for `budRM3` at the `Rat` num/den projections. -/
lemma budRM3_div_eq (a0N a1N a2N a3N a4N a5N remN : ℤ)
    {a0 a1 a2 a3 a4 a5 rem : ℚ} (εα εθ εφ : ℚ) (s : ℕ)
    (h0 : a0 = (a0N : ℚ) / 10 ^ s) (h1 : a1 = (a1N : ℚ) / 10 ^ s)
    (h2 : a2 = (a2N : ℚ) / 10 ^ s) (h3 : a3 = (a3N : ℚ) / 10 ^ s)
    (h4 : a4 = (a4N : ℚ) / 10 ^ s) (h5 : a5 = (a5N : ℚ) / 10 ^ s)
    (hrem : rem = (remN : ℚ) / 10 ^ s) :
    εα * a0 + εθ * a1 + εφ * a2
        + (1/2) * (εα ^ 2 * a0 + 2 * (εα * εθ) * a1 + 2 * (εα * εφ) * a2
          + εθ ^ 2 * a3 + 2 * (εθ * εφ) * a4 + εφ ^ 2 * a5)
        + rem * (εα + εθ + εφ) ^ 3 / 6
      = ((budRM3 a0N a1N a2N a3N a4N a5N remN
            εα.num εα.den εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ)
        / (6 * ((εα.den : ℚ) * (εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 * 10 ^ s) :=
  budRM3_div_eq' a0N a1N a2N a3N a4N a5N remN εα.num εθ.num εφ.num
    εα.den εθ.den εφ.den s εα.den_nz εθ.den_nz εφ.den_nz
    (Rat.num_div_den εα).symm (Rat.num_div_den εθ).symm (Rat.num_div_den εφ).symm
    h0 h1 h2 h3 h4 h5 hrem

/-! ## `ΔrotRMℚ` over `app6` fields -/

/-- The scalar `ΔrotRMℚ` on `app6` fields. -/
@[inline] def dRotRMs (su : UpperSqrt) (slack : ℚ) (q : App6) (εα εθ εφ : ℚ) : ℚ :=
  εα * (su.f (q.a0 * q.a0 + q.a1 * q.a1) + slack)
  + εθ * (su.f (q.b0 * q.b0 + q.b1 * q.b1) + slack)
  + εφ * (su.f (q.c0 * q.c0 + q.c1 * q.c1) + slack)
  + (1/2) * (εα ^ 2 * (su.f (q.a0 * q.a0 + q.a1 * q.a1) + slack)
      + 2 * (εα * εθ) * (su.f (q.b0 * q.b0 + q.b1 * q.b1) + slack)
      + 2 * (εα * εφ) * (su.f (q.c0 * q.c0 + q.c1 * q.c1) + slack)
      + εθ ^ 2 * (su.f (q.d0 * q.d0 + q.d1 * q.d1) + slack)
      + 2 * (εθ * εφ) * (su.f (q.e0 * q.e0 + q.e1 * q.e1) + slack)
      + εφ ^ 2 * (su.f (q.f0 * q.f0 + q.f1 * q.f1) + slack))
  + (εα + εθ + εφ) ^ 3 / 6

lemma dRotRMs_eq (su : UpperSqrt) (θ φ : ℚ) (v : Fin 3 → ℚ) (εα εθ εφ : ℚ) :
    ΔrotRMℚ su θ φ v εα εθ εφ
      = dRotRMs su (3 * κℚ) (app6 (fam2 θ φ) v) εα εθ εφ := by
  unfold ΔrotRMℚ dRotRMs
  simp only [norm2_eq, app6_a0, app6_a1, app6_b0, app6_b1, app6_c0, app6_c1,
    app6_d0, app6_d1, app6_e0, app6_e1, app6_f0, app6_f1]

/-! ## The δ₂ fraction -/

/-- Common denominator of the three `BoundDelta₂ℚi` numerators. -/
def δ₂DZ (row : Row) : ℤ :=
  10 ^ 16 * (6 * ((row.εα.den : ℤ) * row.εθ₁.den * row.εφ₁.den) ^ 3)
    * (6 * ((row.εθ₂.den : ℤ) * row.εφ₂.den) ^ 3)

/-- Integer numerator of `Row.BoundDelta₂ℚi i` at denominator `δ₂DZ`. -/
def δ₂BZ (row : Row) (i : Fin 3) : ℤ :=
  let p := row.interval.centerPose
  let zP := app6N (sinNum13 p.θ₁) (cosNum13 p.θ₁) (sinNum13 p.φ₁)
    (cosNum13 p.φ₁) (row.Pi i)
  let zQ := app6N (sinNum13 p.θ₂) (cosNum13 p.θ₂) (sinNum13 p.φ₂)
    (cosNum13 p.φ₂) (row.Qi i)
  let sa := sinNum13 p.α
  let ca := cosNum13 p.α
  let H0 := ca * zP.a0 - sa * zP.a1 - 10 ^ 13 * zQ.a0
  let H1 := sa * zP.a0 + ca * zP.a1 - 10 ^ 13 * zQ.a1
  let hd := sqrtNum110 (H0 * H0 + H1 * H1) + 6 * 10 ^ 6
  let W3 : ℤ := 6 * ((row.εα.den : ℤ) * row.εθ₁.den * row.εφ₁.den) ^ 3
  let W2 : ℤ := 6 * ((row.εθ₂.den : ℤ) * row.εφ₂.den) ^ 3
  let nRM := budRM3 (sqrtNum84 (zP.a0 * zP.a0 + zP.a1 * zP.a1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.b0 * zP.b0 + zP.b1 * zP.b1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.c0 * zP.c0 + zP.c1 * zP.c1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.d0 * zP.d0 + zP.d1 * zP.d1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.e0 * zP.e0 + zP.e1 * zP.e1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.f0 * zP.f0 + zP.f1 * zP.f1) + 3 * 10 ^ 6)
    (10 ^ 16) row.εα.num row.εα.den row.εθ₁.num row.εθ₁.den
    row.εφ₁.num row.εφ₁.den
  let nM := budN (sqrtNum84 (zQ.b0 * zQ.b0 + zQ.b1 * zQ.b1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.c0 * zQ.c0 + zQ.c1 * zQ.c1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.d0 * zQ.d0 + zQ.d1 * zQ.d1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.e0 * zQ.e0 + zQ.e1 * zQ.e1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.f0 * zQ.f0 + zQ.f1 * zQ.f1) + 3 * 10 ^ 6)
    (10 ^ 16) row.εθ₂.num row.εθ₂.den row.εφ₂.num row.εφ₂.den
  hd * (W3 * W2) + nRM * W2 + nM * W3

/-- The unreduced `δ₂` fraction: `Row.δ₂ = fst / snd` with `0 < snd`. -/
def _root_.Noperthedron.Solution.Row.δ₂PairZ (row : Row) : ℤ × ℤ :=
  (max (δ₂BZ row 0) (max (δ₂BZ row 1) (δ₂BZ row 2)) * 10 ^ 10 + 2 * δ₂DZ row,
   2 * δ₂DZ row * 10 ^ 10)

section DeltaBridge

/-- Convert the three-angle budget as a whole, using the same norm-atom
bridge as the two-angle budget in `Local2Nat`. -/
private lemma dRotRMs_intCast (z : App6N) (εα εθ εφ : ℚ) :
    dRotRMs sqrtApprox16.upper_sqrt (3 * κℚ) (app6QofN z) εα εθ εφ
      = ((budRM3 (sqrtNum84 (z.a0 * z.a0 + z.a1 * z.a1) + 3 * 10 ^ 6)
          (sqrtNum84 (z.b0 * z.b0 + z.b1 * z.b1) + 3 * 10 ^ 6)
          (sqrtNum84 (z.c0 * z.c0 + z.c1 * z.c1) + 3 * 10 ^ 6)
          (sqrtNum84 (z.d0 * z.d0 + z.d1 * z.d1) + 3 * 10 ^ 6)
          (sqrtNum84 (z.e0 * z.e0 + z.e1 * z.e1) + 3 * 10 ^ 6)
          (sqrtNum84 (z.f0 * z.f0 + z.f1 * z.f1) + 3 * 10 ^ 6)
          (10 ^ 16) εα.num εα.den εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ)
        / (6 * ((εα.den : ℚ) * εθ.den * εφ.den) ^ 3 * 10 ^ 16) := by
  have hκ : (3 * κℚ : ℚ) = ((3 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by
    norm_num [κℚ]
  unfold dRotRMs
  simp only [app6QofN]
  simpa only [one_mul] using budRM3_div_eq _ _ _ _ _ _ (10 ^ 16) (rem := 1) εα εθ εφ 16
    (upper_f_pair42 z.a0 z.a1 _ hκ) (upper_f_pair42 z.b0 z.b1 _ hκ)
    (upper_f_pair42 z.c0 z.c1 _ hκ) (upper_f_pair42 z.d0 z.d1 _ hκ)
    (upper_f_pair42 z.e0 z.e1 _ hκ) (upper_f_pair42 z.f0 z.f1 _ hκ)
    (by norm_num)

/-- Express the rotated displacement in applied-family coordinates before
converting either family to integers. -/
private lemma displacement_norm (p : Pose ℚ) (P Q : Fin 3 → ℚ) :
    sqrtApprox16.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ P) - p.rotM₂ℚ Q)
      = RationalApprox.sqrtℚUp16
        ((cosℚ p.α * (app6 (fam2 p.θ₁ p.φ₁) P).a0
          - sinℚ p.α * (app6 (fam2 p.θ₁ p.φ₁) P).a1
          - (app6 (fam2 p.θ₂ p.φ₂) Q).a0) ^ 2
        + (sinℚ p.α * (app6 (fam2 p.θ₁ p.φ₁) P).a0
          + cosℚ p.α * (app6 (fam2 p.θ₁ p.φ₁) P).a1
          - (app6 (fam2 p.θ₂ p.φ₂) Q).a1) ^ 2) := by
  rw [norm2_eq]
  simp only [app6_a0, app6_a1, Pose.rotRℚ, Pose.rotM₁ℚ, Pose.rotM₂ℚ,
    RationalApprox.rotRℚ, RationalApprox.rotMℚ, Matrix.toLin'_apply,
    RationalApprox.rotRℚ_mat, Matrix.cons_mulVec, Matrix.cons_dotProduct,
    Matrix.empty_mulVec, Matrix.dotProduct_of_isEmpty, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, neg_mul, Pi.sub_apply, sub_eq_add_neg, pow_two]
  rfl

/-- `Row.BoundDelta₂ℚi` as the integer fraction. -/
private lemma boundDelta_bridge (row : Row) (i : Fin 3) :
    row.BoundDelta₂ℚi i = ((δ₂BZ row i : ℤ) : ℚ) / ((δ₂DZ row : ℤ) : ℚ) := by
  have dα : ((row.εα.den : ℚ)) ≠ 0 := by exact_mod_cast row.εα.den_nz
  have dθ1 : ((row.εθ₁.den : ℚ)) ≠ 0 := by exact_mod_cast row.εθ₁.den_nz
  have dφ1 : ((row.εφ₁.den : ℚ)) ≠ 0 := by exact_mod_cast row.εφ₁.den_nz
  have dθ2 : ((row.εθ₂.den : ℚ)) ≠ 0 := by exact_mod_cast row.εθ₂.den_nz
  have dφ2 : ((row.εφ₂.den : ℚ)) ≠ 0 := by exact_mod_cast row.εφ₂.den_nz
  unfold Row.BoundDelta₂ℚi δ₂BZ δ₂DZ
  dsimp only
  simp only [Function.comp_apply]
  set p : Pose ℚ := row.interval.centerPose with hp
  set Pv : Fin 3 → ℚ := pythonVertexA (row.Pi i) with hPv
  set Qv : Fin 3 → ℚ := pythonVertexA (row.Qi i) with hQv
  set zP : App6N := app6N (sinNum13 p.θ₁) (cosNum13 p.θ₁) (sinNum13 p.φ₁)
    (cosNum13 p.φ₁) (row.Pi i) with hzP
  set zQ : App6N := app6N (sinNum13 p.θ₂) (cosNum13 p.θ₂) (sinNum13 p.φ₂)
    (cosNum13 p.φ₂) (row.Qi i) with hzQ
  have hAP := app6_intCast p.θ₁ p.φ₁ (row.Pi i)
  have hAQ := app6_intCast p.θ₂ p.φ₂ (row.Qi i)
  rw [← hzP] at hAP
  rw [← hzQ] at hAQ
  -- Convert the displacement and the two rotation budgets independently.
  have hhead : sqrtApprox16.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ Pv) - p.rotM₂ℚ Qv)
        + 6 * κℚ
      = ((sqrtNum110 ((cosNum13 p.α * zP.a0 - sinNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a0)
            * (cosNum13 p.α * zP.a0 - sinNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a0)
          + (sinNum13 p.α * zP.a0 + cosNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a1)
            * (sinNum13 p.α * zP.a0 + cosNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a1))
          + 6 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by
    rw [displacement_norm, hAP, hAQ]
    simp only [app6QofN]
    rw [← RationalApprox.sinNum13_div_eq p.α, ← RationalApprox.cosNum13_div_eq p.α]
    have scaled (s c x0 x1 y0 y1 : ℤ) :
        ((c : ℚ) / 10 ^ 13 * ((x0 : ℚ) / 10 ^ 42)
            - (s : ℚ) / 10 ^ 13 * ((x1 : ℚ) / 10 ^ 42) - (y0 : ℚ) / 10 ^ 42) ^ 2
          + ((s : ℚ) / 10 ^ 13 * ((x0 : ℚ) / 10 ^ 42)
            + (c : ℚ) / 10 ^ 13 * ((x1 : ℚ) / 10 ^ 42) - (y1 : ℚ) / 10 ^ 42) ^ 2
        = (((c * x0 - s * x1 - 10 ^ 13 * y0) * (c * x0 - s * x1 - 10 ^ 13 * y0)
            + (s * x0 + c * x1 - 10 ^ 13 * y1) * (s * x0 + c * x1 - 10 ^ 13 * y1) : ℤ) : ℚ)
          / 10 ^ 110 := by push_cast; ring
    rw [scaled, sqrtℚUp16_intCast_div110]
    norm_num [κℚ]
    ring
  rw [hhead, dRotRMs_eq, hAP, dRotRMs_intCast,
    RationalApprox.ΔrotMℚ, dRotMs_eq, hAQ,
    dRotMs_intCast zQ (3 * 10 ^ 6) (10 ^ 16) row.εθ₂ row.εφ₂
      (by norm_num [κℚ]) (by norm_num)]
  push_cast
  field_simp
  ring

end DeltaBridge

/-- `Finset.max'` of a `Fin 3` image as a nested `max`. -/
private lemma max'_image_fin3 (f : Fin 3 → ℚ) :
    Finset.max' (Finset.image f Finset.univ)
        (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)
      = max (f 0) (max (f 1) (f 2)) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    fin_cases j
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  · refine max_le (Finset.le_max' _ _ ?_) (max_le (Finset.le_max' _ _ ?_)
      (Finset.le_max' _ _ ?_)) <;>
      exact Finset.mem_image_of_mem f (Finset.mem_univ _)

lemma δ₂DZ_pos (row : Row) : 0 < δ₂DZ row := by
  unfold δ₂DZ
  have h1 := row.εα.pos
  have h2 := row.εθ₁.pos
  have h3 := row.εφ₁.pos
  have h4 := row.εθ₂.pos
  have h5 := row.εφ₂.pos
  positivity

lemma _root_.Noperthedron.Solution.Row.δ₂PairZ_snd_pos (row : Row) : 0 < (row.δ₂PairZ).2 := by
  unfold Row.δ₂PairZ
  have := δ₂DZ_pos row
  positivity

/-- The exact-value bridge: `Row.δ₂` is the unreduced integer fraction. -/
theorem _root_.Noperthedron.Solution.Row.δ₂PairZ_eq (row : Row) :
    Row.δ₂ row = (((row.δ₂PairZ).1 : ℤ) : ℚ) / (((row.δ₂PairZ).2 : ℤ) : ℚ) := by
  have hD := δ₂DZ_pos row
  have hDQ : (0 : ℚ) < ((δ₂DZ row : ℤ) : ℚ) := by exact_mod_cast hD
  unfold Row.δ₂ Row.δ₂PairZ
  rw [max'_image_fin3, boundDelta_bridge, boundDelta_bridge, boundDelta_bridge]
  rw [max_div_div_right hDQ.le, max_div_div_right hDQ.le]
  rw [show (κℚ : ℚ) = 1 / 10 ^ 10 from rfl]
  have hmax : ((max (δ₂BZ row 0) (max (δ₂BZ row 1) (δ₂BZ row 2)) : ℤ) : ℚ)
      = max ((δ₂BZ row 0 : ℤ) : ℚ) (max ((δ₂BZ row 1 : ℤ) : ℚ) ((δ₂BZ row 2 : ℤ) : ℚ)) := by
    push_cast
    rfl
  rw [← hmax]
  push_cast
  field_simp
  ring

end Noperthedron.Solution.Local2Nat

namespace Noperthedron.Solution

open Local2Nat in
/-- `Row.ValidLocal₂` decided with the δ₂ fraction substituted into the
`Bε₂ℚ` conjunct, so the kernel never evaluates the ℚ definition of
`Row.δ₂` (the offset tier then receives the unreduced fraction and pays a
single `Rat` normalization). -/
instance (priority := 10800) (row : Row) : Decidable (Row.ValidLocal₂ row) :=
  decidable_of_iff
    (row.nodeType = 2 ∧
      row.interval.centerPose ∈ fourInterval ℚ ∧
      (∃ s : TriangleSymmetry,
        s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)) ∧
      Local.TriangleQ.Aε₂ℚσ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
        row.εθ₁ row.εφ₁ 0 ∧
      Local.TriangleQ.Aε₂ℚσ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
        row.εθ₂ row.εφ₂ row.sigma_Q.val ∧
      Local.TriangleQ.Spanning₂ℚ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
        row.εθ₁ row.εφ₁ ∧
      Local.TriangleQ.Spanning₂ℚ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
        row.εθ₂ row.εφ₂ ∧
      0 < row.r ∧
      RationalApprox.LocalTheorem.BoundR₂ℚ row.r row.interval.centerPose
        (pythonVertexA ∘ row.Qi) row.εθ₂ row.εφ₂ RationalApprox.sqrtApprox16 ∧
      Local.TriangleQ.Bε₂ℚ row.Qi pythonVertexA row.interval.centerPose
        row.εθ₂ row.εφ₂ ((((row.δ₂PairZ).1 : ℤ) : ℚ) / (((row.δ₂PairZ).2 : ℤ) : ℚ))
        row.r RationalApprox.sqrtApprox16.upper_sqrt)
    (by rw [← Row.δ₂PairZ_eq row]; exact (Row.validLocal₂_iff row).symm)

end Noperthedron.Solution

end
