import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Set.Operations
import Noperthedron.Global
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.BoundsKappa

open scoped RealInnerProductSpace

namespace RationalApprox.GlobalTheorem

/-! ### Per-pose hoisted entries for `Gℚ`/`Hℚ`

Both certificate sides evaluate a handful of `(matrix chain)ᵀ·w` 3-vectors
that depend only on the pose and `w`, then dot them against many vertices.
We hoist those 3-vectors out to per-pose work (`hEntries`/`gEntries`) and
round each component down to a multiple of `10⁻¹³` (`hEntriesR`/`gEntriesR`,
see `round13v`): the trig values `sinℚ`/`cosℚ` have denominators `10¹³`, so
the raw hoisted vectors have denominators around `10³⁶` and every per-vertex
dot product would run on large-integer gcds. The rounding perturbs each dot
product by at most `3(1+κ)/10¹³`, which is absorbed into the `3κ`/`4κ`
budgets of the soundness lemmas `H_le_Hℚ`/`Gℚ_le_G` below (whose ingredient
bounds `bounds_kappa_*` are proved with `≈ κ` to spare). -/

namespace Gℚ_gt_maxHℚ

/-- Pre-transposed `Mᵀ·w` 3-vectors so that each per-`P` `Hℚ` evaluation is just
three small dot products instead of three matrix-vector multiplies. -/
private structure HEntries : Type where
  m2tw  : Fin 3 → ℚ
  m2θtw : Fin 3 → ℚ
  m2φtw : Fin 3 → ℚ

@[inline] private def hEntries (p : Pose ℚ) (w : Fin 2 → ℚ) : HEntries :=
  let st := RationalApprox.sinℚ p.θ₂
  let ct := RationalApprox.cosℚ p.θ₂
  let sp := RationalApprox.sinℚ p.φ₂
  let cp := RationalApprox.cosℚ p.φ₂
  let w0 := w 0
  let w1 := w 1
  -- M₂  = [[-st,      ct,       0    ],
  --        [-ct*cp,   -st*cp,   sp   ]]
  -- M₂θ = [[-ct,     -st,       0    ],
  --        [ st*cp,  -ct*cp,    0    ]]
  -- M₂φ = [[ 0,       0,        0    ],
  --        [ ct*sp,   st*sp,    cp   ]]
  -- (Mᵀ·w)[j] = ∑ i, M[i][j] * w[i]
  ⟨ ![-st * w0 + (-ct * cp) * w1,    ct * w0 + (-st * cp) * w1,    sp * w1],
    ![-ct * w0 + ( st * cp) * w1,   -st * w0 + (-ct * cp) * w1,    0],
    ![ (ct * sp) * w1,                (st * sp) * w1,              cp * w1] ⟩

/-- `hEntries` with each hoisted vector rounded down to multiples of `10⁻¹³`,
so the per-`P` dot products run on small denominators. (The checker reads
these through `HEntries.scalars`, which forces each component once.) -/
@[inline] private def hEntriesR (p : Pose ℚ) (w : Fin 2 → ℚ) : HEntries :=
  let e := hEntries p w
  ⟨round13v e.m2tw, round13v e.m2θtw, round13v e.m2φtw⟩

private lemma m2tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2tw ⬝ᵥ P = p.rotM₂ℚ P ⬝ᵥ w := by
  unfold Pose.rotM₂ℚ RationalApprox.rotMℚ RationalApprox.rotMℚ_mat
  rw [Matrix.toLin'_apply]
  simp [hEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m2θtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θtw ⬝ᵥ P = p.rotM₂θℚ P ⬝ᵥ w := by
  unfold Pose.rotM₂θℚ RationalApprox.rotMθℚ RationalApprox.rotMθℚ_mat
  rw [Matrix.toLin'_apply]
  simp [hEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m2φtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2φtw ⬝ᵥ P = p.rotM₂φℚ P ⬝ᵥ w := by
  unfold Pose.rotM₂φℚ RationalApprox.rotMφℚ RationalApprox.rotMφℚ_mat
  rw [Matrix.toLin'_apply]
  simp [hEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

@[inline] private def fastH (entries : HEntries) (ε : ℚ) (kappaTerm : ℚ) (P : Fin 3 → ℚ) : ℚ :=
  entries.m2tw ⬝ᵥ P + ε * (|entries.m2θtw ⬝ᵥ P| + |entries.m2φtw ⬝ᵥ P|) + 2 * ε^2 + kappaTerm

/-- Pre-computed `(M_combined)ᵀ·w` 3-vectors for the four matrix chains in
`Gℚ` (`R·M₁`, `R'·M₁`, `R·M₁θ`, `R·M₁φ`). With these, each chain in `Gℚ`
collapses to a single 3-element dot product against `S`. -/
private structure GEntries : Type where
  m1RTw   : Fin 3 → ℚ  -- (R · M₁)ᵀ · w  for `p.innerℚ S ⬝ᵥ w`
  m1R'Tw  : Fin 3 → ℚ  -- (R' · M₁)ᵀ · w for `p.rotR'ℚ (p.rotM₁ℚ S) ⬝ᵥ w`
  m1θRTw  : Fin 3 → ℚ  -- (R · M₁θ)ᵀ · w for `p.rotRℚ (p.rotM₁θℚ S) ⬝ᵥ w`
  m1φRTw  : Fin 3 → ℚ  -- (R · M₁φ)ᵀ · w for `p.rotRℚ (p.rotM₁φℚ S) ⬝ᵥ w`

@[inline] private def gEntries (p : Pose ℚ) (w : Fin 2 → ℚ) : GEntries :=
  let st1 := RationalApprox.sinℚ p.θ₁
  let ct1 := RationalApprox.cosℚ p.θ₁
  let sp1 := RationalApprox.sinℚ p.φ₁
  let cp1 := RationalApprox.cosℚ p.φ₁
  let sa  := RationalApprox.sinℚ p.α
  let ca  := RationalApprox.cosℚ p.α
  let w0 := w 0
  let w1 := w 1
  -- Rᵀ · w = (ca·w0 + sa·w1, -sa·w0 + ca·w1)
  let u0  := ca * w0 + sa * w1
  let u1  := -sa * w0 + ca * w1
  -- R'ᵀ · w = (-sa·w0 + ca·w1, -ca·w0 + (-sa)·w1)
  let up0 := -sa * w0 + ca * w1
  let up1 := -ca * w0 + (-sa) * w1
  -- M₁ᵀ · u: uses (M₁[j][i])
  -- M₁ = [[-st1, ct1, 0], [-ct1*cp1, -st1*cp1, sp1]]
  ⟨ ![-st1 * u0 + (-ct1 * cp1) * u1,
       ct1 * u0 + (-st1 * cp1) * u1,
       sp1 * u1],
    -- M₁ᵀ · u'
    ![-st1 * up0 + (-ct1 * cp1) * up1,
       ct1 * up0 + (-st1 * cp1) * up1,
       sp1 * up1],
    -- M₁θᵀ · u; M₁θ = [[-ct1, -st1, 0], [st1*cp1, -ct1*cp1, 0]]
    ![-ct1 * u0 + (st1 * cp1) * u1,
      -st1 * u0 + (-ct1 * cp1) * u1,
       0],
    -- M₁φᵀ · u; M₁φ = [[0, 0, 0], [ct1*sp1, st1*sp1, cp1]]
    ![(ct1 * sp1) * u1,
      (st1 * sp1) * u1,
       cp1 * u1] ⟩

/-- `gEntries` with each hoisted vector rounded down to multiples of `10⁻¹³`.
(Each component is read once per row by `fastG`.) -/
@[inline] private def gEntriesR (p : Pose ℚ) (w : Fin 2 → ℚ) : GEntries :=
  let e := gEntries p w
  ⟨round13v e.m1RTw, round13v e.m1R'Tw, round13v e.m1θRTw, round13v e.m1φRTw⟩

private lemma m1RTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1RTw ⬝ᵥ S = p.innerℚ S ⬝ᵥ w := by
  show _ = (Pose.rotRℚ p (Pose.rotM₁ℚ p S)) ⬝ᵥ w
  unfold Pose.rotRℚ Pose.rotM₁ℚ RationalApprox.rotRℚ RationalApprox.rotMℚ
        RationalApprox.rotRℚ_mat RationalApprox.rotMℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m1R'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1R'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁ℚ S) ⬝ᵥ w := by
  unfold Pose.rotR'ℚ Pose.rotM₁ℚ RationalApprox.rotR'ℚ RationalApprox.rotMℚ
        RationalApprox.rotR'ℚ_mat RationalApprox.rotMℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m1θRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θℚ S) ⬝ᵥ w := by
  unfold Pose.rotRℚ Pose.rotM₁θℚ RationalApprox.rotRℚ RationalApprox.rotMθℚ
        RationalApprox.rotRℚ_mat RationalApprox.rotMθℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m1φRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁φℚ S) ⬝ᵥ w := by
  unfold Pose.rotRℚ Pose.rotM₁φℚ RationalApprox.rotRℚ RationalApprox.rotMφℚ
        RationalApprox.rotRℚ_mat RationalApprox.rotMφℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

@[inline] private def fastG (entries : GEntries) (ε : ℚ) (S : Fin 3 → ℚ) : ℚ :=
  entries.m1RTw ⬝ᵥ S -
   (ε * (|entries.m1R'Tw ⬝ᵥ S| + |entries.m1θRTw ⬝ᵥ S| + |entries.m1φRTw ⬝ᵥ S|)
     + 9 * ε^2 / 2 + 4 * κℚ * (1 + 3 * ε))

/-- The rounded hoisted `H`-side vectors as strict scalar fields. A
`Fin 3 → ℚ` value is a closure whose components (including their `round13`
calls) are re-evaluated on every access; structure-constructor arguments are
evaluated once, at construction, so the checker's per-`P` loop reads
precomputed scalars. -/
private structure HScalars : Type where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  b0 : ℚ
  b1 : ℚ
  b2 : ℚ
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ

@[inline] private def HEntries.scalars (e : HEntries) : HScalars :=
  ⟨e.m2tw 0, e.m2tw 1, e.m2tw 2,
   e.m2θtw 0, e.m2θtw 1, e.m2θtw 2,
   e.m2φtw 0, e.m2φtw 1, e.m2φtw 2⟩

/-- `fastH` on precomputed scalars, with the dot products written out. Takes
the vertex coordinates as scalars so each is read (a `ℚ` division for the
table's vertex functions) only once per vertex. -/
@[inline] private def fastHs (e : HScalars) (ε : ℚ) (kappaTerm : ℚ) (p0 p1 p2 : ℚ) : ℚ :=
  e.a0 * p0 + e.a1 * p1 + e.a2 * p2
    + ε * (|e.b0 * p0 + e.b1 * p1 + e.b2 * p2| + |e.c0 * p0 + e.c1 * p1 + e.c2 * p2|)
    + 2 * ε^2 + kappaTerm

private lemma fastHs_scalars_eq (e : HEntries) (ε kt : ℚ) (P : Fin 3 → ℚ) :
    fastHs e.scalars ε kt (P 0) (P 1) (P 2) = fastH e ε kt P := by
  simp only [fastHs, HEntries.scalars, fastH, dotProduct, Fin.sum_univ_three]

end Gℚ_gt_maxHℚ

open Gℚ_gt_maxHℚ in
/--
A measure of how far an inner-shadow vertex S can "stick out".

The four hoisted `(R·M₁)ᵀ·w`-style 3-vectors are rounded down to multiples of
`10⁻¹³` (`gEntriesR`); the `4κℚ(1+3ε)` term absorbs both the `sinℚ`/`cosℚ`
approximation error and this rounding (see `Gℚ_le_G`).
-/
def Gℚ (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) : ℚ :=
  fastG (gEntriesR p w) ε S

open Gℚ_gt_maxHℚ in
/--
A measure of how far an outer-shadow vertex P can "reach" along w.

The hoisted `M₂ᵀ·w`-style 3-vectors are rounded down to multiples of `10⁻¹³`
(`hEntriesR`); the `3κℚ(1+2ε)` term absorbs both the `sinℚ`/`cosℚ`
approximation error and this rounding (see `H_le_Hℚ`).
-/
def Hℚ (p : Pose ℚ) (ε : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) : ℚ :=
  fastH (hEntriesR p w) ε (3 * κℚ * (1 + 2 * ε)) P

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
def maxHℚ {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (ε : ℚ) (w : Fin 2 → ℚ) : ℚ :=
  Finset.image (Hℚ p ε w ∘ poly.v) Finset.univ  |>.max' <| by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr ne

private lemma fastG_eq_Gℚ (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ.fastG (Gℚ_gt_maxHℚ.gEntriesR p w) ε S = Gℚ p ε S w := rfl

private lemma fastH_eq_Hℚ (p : Pose ℚ) (ε : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    Gℚ_gt_maxHℚ.fastH (Gℚ_gt_maxHℚ.hEntriesR p w) ε (3 * κℚ * (1 + 2 * ε)) P = Hℚ p ε w P :=
  rfl

open Gℚ_gt_maxHℚ in
/-- Bool-valued `Gℚ > maxHℚ` check that hoists the trig partial sums and the
rounded `Mᵀ·w` 3-vectors to per-pose work for both `Gℚ` and `Hℚ`; the
`∀ P ∈ poly.v` loop then only does small-denominator dot products. -/
def Gℚ_gt_maxHℚ_check {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ)
    (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) : Bool :=
  let hscalars := (hEntriesR p w).scalars
  let g := fastG (gEntriesR p w) ε S
  let kappaTerm := 3 * κℚ * (1 + 2 * ε)
  decide <| ∀ k : ι, g > fastHs hscalars ε kappaTerm (poly.v k 0) (poly.v k 1) (poly.v k 2)

theorem Gℚ_gt_maxHℚ_check_iff {ι : Type} [Fintype ι] [DecidableEq ι] [ne : Nonempty ι]
    (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ)
    (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ_check p ε S poly w = true ↔
      Gℚ p ε S w > maxHℚ p poly ε w := by
  unfold Gℚ_gt_maxHℚ_check maxHℚ
  simp only [decide_eq_true_eq]
  rw [fastG_eq_Gℚ]
  constructor
  · intro hAll
    show (Finset.image (Hℚ p ε w ∘ poly.v) Finset.univ).max' _ < Gℚ p ε S w
    rw [Finset.max'_lt_iff]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have := hAll k
    rw [Gℚ_gt_maxHℚ.fastHs_scalars_eq, fastH_eq_Hℚ] at this
    exact this
  · intro hLt k
    rw [Gℚ_gt_maxHℚ.fastHs_scalars_eq, fastH_eq_Hℚ]
    apply lt_of_le_of_lt _ hLt
    apply Finset.le_max'
    rw [Finset.mem_image]
    exact ⟨k, Finset.mem_univ k, rfl⟩

/--
A compact way of saying "the pose satisfies the rational global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyhedron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure RationalGlobalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_) (p : Pose ℚ) (ε : ℚ) : Type where
  j : ι
  p_in_4 : p ∈ fourInterval ℚ
  w : Fin 2 → ℚ
  w_unit : ‖toR2 w‖ = 1
  exceeds : Gℚ p ε (poly_.v j) w > maxHℚ p poly_ ε w

private lemma abs_le_abs_add_of_norm_sub_le {a b C : ℝ} (h : ‖a - b‖ ≤ C) : |a| ≤ |b| + C := by
  linarith [abs_sub_abs_le_abs_sub a b, (Real.norm_eq_abs _).symm ▸ h]

/-- The coordinates of a κ-approximation `P_` of a vector of norm ≤ 1 have
`∑ i, |P_ i| ≤ 3(1+κℚ)`. -/
private lemma sum_abs_le_of_approx {P : ℝ³} {P_ : Fin 3 → ℚ}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - toR3 P_‖ ≤ κ) :
    ∑ i, |P_ i| ≤ 3 * (1 + κℚ) := by
  have hPnorm : ‖toR3 P_‖ ≤ 1 + κ := by
    have h := norm_le_insert P (toR3 P_)
    linarith
  have hcoord : ∀ i, |P_ i| ≤ 1 + κℚ := by
    intro i
    have h1 : |(P_ i : ℝ)| ≤ ‖toR3 P_‖ := by
      have h := PiLp.norm_apply_le (toR3 P_) i
      simpa only [toR3, WithLp.ofLp_toLp, Real.norm_eq_abs] using h
    have h2 : |(P_ i : ℝ)| ≤ 1 + κ := h1.trans hPnorm
    rw [← cast_κℚ] at h2
    exact_mod_cast h2
  rw [Fin.sum_univ_three]
  linarith [hcoord 0, hcoord 1, hcoord 2]

/-- Absorb the `round13v` rounding of a hoisted 3-vector into a κ-scale bound:
rounding perturbs the dot product against `P_` by at most `3(1+κ)/10¹³`. -/
private lemma norm_sub_round13v_dot_le {x : ℝ} {v P_ : Fin 3 → ℚ} {c : ℝ}
    (hbase : ‖x - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ c)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ c + 3 * (1 + κ) / 10 ^ 13 := by
  have hq : |round13v v ⬝ᵥ P_ - v ⬝ᵥ P_| ≤ 3 * (1 + κℚ) / 10 ^ 13 :=
    (abs_round13v_dot_sub_le v P_).trans (by gcongr)
  have hr : ‖((round13v v ⬝ᵥ P_ : ℚ) : ℝ) - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * (1 + κ) / 10 ^ 13 := by
    rw [Real.norm_eq_abs, ← Rat.cast_sub, ← Rat.cast_abs, ← cast_κℚ]
    exact_mod_cast hq
  calc ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖
      = ‖(x - ((v ⬝ᵥ P_ : ℚ) : ℝ)) -
          (((round13v v ⬝ᵥ P_ : ℚ) : ℝ) - ((v ⬝ᵥ P_ : ℚ) : ℝ))‖ := by
        congr 1; ring
    _ ≤ ‖x - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ +
        ‖((round13v v ⬝ᵥ P_ : ℚ) : ℝ) - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ := norm_sub_le _ _
    _ ≤ c + 3 * (1 + κ) / 10 ^ 13 := add_le_add hbase hr

/-- `norm_sub_round13v_dot_le` specialised to the `H`-side budget: a
`bounds_kappa_M`-style base bound plus the rounding perturbation is ≤ `3κ`. -/
private lemma norm_sub_round13v_dot_le₃ {x : ℝ} {v P_ : Fin 3 → ℚ}
    (hbase : ‖x - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 2 * κ + κ ^ 2)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
  (norm_sub_round13v_dot_le hbase hsum).trans (by unfold κ; norm_num)

/-- `norm_sub_round13v_dot_le` specialised to the `G`-side budget: a
`bounds_kappa_RM`-style base bound plus the rounding perturbation is ≤ `4κ`. -/
private lemma norm_sub_round13v_dot_le₄ {x : ℝ} {v P_ : Fin 3 → ℚ}
    (hbase : ‖x - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ + 3 * κ ^ 2 + κ ^ 3)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
  (norm_sub_round13v_dot_le hbase hsum).trans (by unfold κ; norm_num)

private lemma Gℚ_le_G {p_ : Pose ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    {S : ℝ³} {S_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hS : ‖S‖ ≤ 1) (hS_approx : ‖S - toR3 S_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains p_) :
    Gℚ p_ ε S_ w ≤ GlobalTheorem.G p_.toReal ε S (toR2 w) := by
  set pbar := p_.toReal with hpbar
  have hsum := sum_abs_le_of_approx hS hS_approx
  unfold Gℚ Gℚ_gt_maxHℚ.fastG GlobalTheorem.G
  rw [show pbar.inner S = pbar.rotR (pbar.rotM₁ S) by rw [Pose.inner_eq_RM]; rfl]
  show _ ≤ ⟪rotR (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
        ((ε : ℝ) * (|⟪rotR' (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    |⟪rotR (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    |⟪rotR (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫|) +
         9 * (ε : ℝ)^2 / 2)
  have h_RM : ‖⟪rotR (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
      (((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1RTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ := by
    refine norm_sub_round13v_dot_le₄ ?_ hsum
    rw [Gℚ_gt_maxHℚ.m1RTw_dot_eq]
    exact bounds_kappa_RM
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_R'M : ‖⟪rotR' (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
      (((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1R'Tw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ := by
    refine norm_sub_round13v_dot_le₄ ?_ hsum
    rw [Gℚ_gt_maxHℚ.m1R'Tw_dot_eq]
    exact bounds_kappa_R'M
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_RMθ : ‖⟪rotR (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
      (((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1θRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ := by
    refine norm_sub_round13v_dot_le₄ ?_ hsum
    rw [Gℚ_gt_maxHℚ.m1θRTw_dot_eq]
    exact bounds_kappa_RMθ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_RMφ : ‖⟪rotR (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
      (((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1φRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ := by
    refine norm_sub_round13v_dot_le₄ ?_ hsum
    rw [Gℚ_gt_maxHℚ.m1φRTw_dot_eq]
    exact bounds_kappa_RMφ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have hi_le : (((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1RTw ⬝ᵥ S_ : ℚ) : ℝ) ≤
               ⟪rotR (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ + 4 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_RM; rw [abs_le] at this
    linarith [this.1]
  have hR'_abs := abs_le_abs_add_of_norm_sub_le h_R'M
  have hRθ_abs := abs_le_abs_add_of_norm_sub_le h_RMθ
  have hRφ_abs := abs_le_abs_add_of_norm_sub_le h_RMφ
  have h_κ : ((κℚ : ℚ) : ℝ) = κ := cast_κℚ
  have hε_real : (0 : ℝ) ≤ ε := mod_cast hε
  show _ ≤ _
  push_cast
  rw [h_κ]
  show _ -
        ((ε : ℝ) * (|(((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1R'Tw ⬝ᵥ S_ : ℚ) : ℝ)| +
                    |(((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1θRTw ⬝ᵥ S_ : ℚ) : ℝ)| +
                    |(((Gℚ_gt_maxHℚ.gEntriesR p_ w).m1φRTw ⬝ᵥ S_ : ℚ) : ℝ)|) +
         9 * ((ε : ℝ))^2 / 2 + 4 * κ * (1 + 3 * ((ε : ℝ)))) ≤ _
  -- `ε * Σ|real| ≤ ε * Σ(|rational| + 4κ)`, then the `4κ(1+3ε)` term closes the gap.
  linarith [hi_le,
    mul_le_mul_of_nonneg_left (add_le_add (add_le_add hR'_abs hRθ_abs) hRφ_abs) hε_real]

private lemma H_le_Hℚ {pbar : Pose ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    {P : ℝ³} {P_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains pbar) :
    GlobalTheorem.H pbar.toReal ε (toR2 w) P ≤ Hℚ pbar ε w P_ := by
  have hsum := sum_abs_le_of_approx hP hP_approx
  unfold GlobalTheorem.H Hℚ Gℚ_gt_maxHℚ.fastH Pose.rotM₂ Pose.rotM₂θ Pose.rotM₂φ
  show ⟪rotM (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫ +
        (ε : ℝ) * (|⟪rotMθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| +
                   |⟪rotMφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫|) +
        2 * (ε : ℝ)^2 ≤ _
  have h_M : ‖⟪rotM (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫ -
      (((Gℚ_gt_maxHℚ.hEntriesR pbar w).m2tw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ := by
    refine norm_sub_round13v_dot_le₃ ?_ hsum
    rw [Gℚ_gt_maxHℚ.m2tw_dot_eq]
    exact bounds_kappa_M
      (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩) hP hP_approx hw
  have h_Mθ : ‖⟪rotMθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫ -
      (((Gℚ_gt_maxHℚ.hEntriesR pbar w).m2θtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ := by
    refine norm_sub_round13v_dot_le₃ ?_ hsum
    rw [Gℚ_gt_maxHℚ.m2θtw_dot_eq]
    exact bounds_kappa_Mθ
      (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩) hP hP_approx hw
  have h_Mφ : ‖⟪rotMφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫ -
      (((Gℚ_gt_maxHℚ.hEntriesR pbar w).m2φtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ := by
    refine norm_sub_round13v_dot_le₃ ?_ hsum
    rw [Gℚ_gt_maxHℚ.m2φtw_dot_eq]
    exact bounds_kappa_Mφ
      (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩) hP hP_approx hw
  have hm_le : ⟪rotM (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫ ≤
               (((Gℚ_gt_maxHℚ.hEntriesR pbar w).m2tw ⬝ᵥ P_ : ℚ) : ℝ) + 3 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_M; rw [abs_le] at this
    linarith [this.2]
  have hθ_abs : |⟪rotMθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| ≤
                |(((Gℚ_gt_maxHℚ.hEntriesR pbar w).m2θtw ⬝ᵥ P_ : ℚ) : ℝ)| + 3 * κ :=
    abs_le_abs_add_of_norm_sub_le h_Mθ
  have hφ_abs : |⟪rotMφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| ≤
                |(((Gℚ_gt_maxHℚ.hEntriesR pbar w).m2φtw ⬝ᵥ P_ : ℚ) : ℝ)| + 3 * κ :=
    abs_le_abs_add_of_norm_sub_le h_Mφ
  have h_κ : ((κℚ : ℚ) : ℝ) = κ := cast_κℚ
  have hε_real : (0 : ℝ) ≤ ε := mod_cast hε
  push_cast
  rw [h_κ]
  -- `ε * Σ|real| ≤ ε * Σ(|rational| + 3κ)`, then the `3κ(1+2ε)` term closes the gap.
  linarith [hm_le, mul_le_mul_of_nonneg_left (add_le_add hθ_abs hφ_abs) hε_real]

/--
[SY25] Theorem 43
-/
theorem rational_global {ι : Type} [Fintype ι] [Nonempty ι]
    (p : Pose ℚ) (ε : ℚ) (hε : 0 ≤ ε)
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_)
    (pc : RationalGlobalTheoremPrecondition poly poly_ happrox p ε) :
    ¬ ∃ q ∈ Metric.closedBall p.toReal ε, RupertPose q poly.hull := by
  set pbar := p.toReal
  have hp4 : (fourInterval ℝ).contains pbar := fourInterval_contains_toReal pc.p_in_4
  -- Step 1: Map S from poly_ to poly via the bijection
  let j := pc.j
  let i := happrox.bijection.symm j
  let S_real := poly.vertices.v i
  have hS_approx : ‖S_real - poly_.toReal.v j‖ ≤ κ := by
    show ‖poly.vertices.v (happrox.bijection.symm j) - poly_.toReal.v j‖ ≤ κ
    have := happrox.approx (happrox.bijection.symm j)
    rwa [Equiv.apply_symm_apply] at this
  have hS_norm : ‖S_real‖ ≤ 1 := poly.vertex_radius_le_one i
  -- Step 2: Show maxH_real ≤ maxHℚ
  have h_maxH_le : GlobalTheorem.maxH pbar poly ε (toR2 pc.w) ≤ ((maxHℚ p poly_ ε pc.w : ℚ) : ℝ) := by
    unfold GlobalTheorem.maxH
    apply Finset.max'_le
    simp only [Function.comp, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨k, rfl⟩
    let k' := happrox.bijection k
    have hk_norm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
    have hk_approx : ‖poly.vertices.v k - poly_.toReal.v k'‖ ≤ κ := happrox.approx k
    have h_le_Hℚ : GlobalTheorem.H pbar ε (toR2 pc.w) (poly.vertices.v k) ≤
                    Hℚ p ε pc.w (poly_.v k') :=
      H_le_Hℚ hε hk_norm
        (show ‖poly.vertices.v k - toR3 (poly_.v k')‖ ≤ κ from hk_approx)
        pc.w_unit pc.p_in_4
    have h_le_max : Hℚ p ε pc.w (poly_.v k') ≤ maxHℚ p poly_ ε pc.w := by
      unfold maxHℚ
      have : (Hℚ p ε pc.w ∘ poly_.v) k' ∈
              Finset.image (Hℚ p ε pc.w ∘ poly_.v) Finset.univ :=
        Finset.mem_image_of_mem _ (Finset.mem_univ k')
      exact Finset.le_max' _ _ this
    have h_le_max_real : ((Hℚ p ε pc.w (poly_.v k') : ℚ) : ℝ) ≤ ((maxHℚ p poly_ ε pc.w : ℚ) : ℝ) :=
      mod_cast h_le_max
    linarith [h_le_Hℚ, h_le_max_real]
  -- Step 3: Build the precondition and apply global_theorem
  exact GlobalTheorem.global_theorem pbar ε (Rat.cast_nonneg.mpr hε) poly {
    Si := i
    w := toR2 pc.w
    w_unit := pc.w_unit
    exceeds := by
      have hG_le := Gℚ_le_G hε hS_norm hS_approx pc.w_unit pc.p_in_4
      have hexceeds_real : ((Gℚ p ε (poly_.v pc.j) pc.w : ℚ) : ℝ) >
                            ((maxHℚ p poly_ ε pc.w : ℚ) : ℝ) := mod_cast pc.exceeds
      linarith [hG_le, hexceeds_real, h_maxH_le]
  }
