import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Set.Operations
import Noperthedron.Global
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.TrigInt
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

/-- Pre-transposed `Mᵀ·w` 3-vectors so that each per-`P` `Hℚ` evaluation is
six small dot products instead of six matrix-vector multiplies. -/
private structure HEntries : Type where
  m2tw   : Fin 3 → ℚ
  m2θtw  : Fin 3 → ℚ
  m2φtw  : Fin 3 → ℚ
  m2θθtw : Fin 3 → ℚ
  m2θφtw : Fin 3 → ℚ
  m2φφtw : Fin 3 → ℚ

@[inline] private def hEntries (p : Pose ℚ) (w : Fin 2 → ℚ) : HEntries :=
  let st := (RationalApprox.sinNum13 p.θ₂ : ℚ) / 10 ^ 13
  let ct := (RationalApprox.cosNum13 p.θ₂ : ℚ) / 10 ^ 13
  let sp := (RationalApprox.sinNum13 p.φ₂ : ℚ) / 10 ^ 13
  let cp := (RationalApprox.cosNum13 p.φ₂ : ℚ) / 10 ^ 13
  let w0 := w 0
  let w1 := w 1
  -- M₂   = [[-st,      ct,       0    ],
  --         [-ct*cp,   -st*cp,   sp   ]]
  -- M₂θ  = [[-ct,     -st,       0    ],
  --         [ st*cp,  -ct*cp,    0    ]]
  -- M₂φ  = [[ 0,       0,        0    ],
  --         [ ct*sp,   st*sp,    cp   ]]
  -- M₂θθ = [[ st,     -ct,       0    ],
  --         [ ct*cp,   st*cp,    0    ]]
  -- M₂θφ = [[ 0,       0,        0    ],
  --         [-st*sp,   ct*sp,    0    ]]
  -- M₂φφ = [[ 0,       0,        0    ],
  --         [ ct*cp,   st*cp,   -sp   ]]
  -- (Mᵀ·w)[j] = ∑ i, M[i][j] * w[i]
  ⟨ ![-st * w0 + (-ct * cp) * w1,    ct * w0 + (-st * cp) * w1,    sp * w1],
    ![-ct * w0 + ( st * cp) * w1,   -st * w0 + (-ct * cp) * w1,    0],
    ![ (ct * sp) * w1,                (st * sp) * w1,              cp * w1],
    ![ st * w0 + (ct * cp) * w1,    -ct * w0 + (st * cp) * w1,     0],
    ![ (-st * sp) * w1,               (ct * sp) * w1,              0],
    ![ (ct * cp) * w1,                (st * cp) * w1,             -sp * w1] ⟩

/-- `hEntries` with each hoisted vector rounded down to multiples of `10⁻¹³`,
so the per-`P` dot products run on small denominators. (The checker reads
these through `HEntries.scalars`, which forces each component once.) -/
@[inline] private def hEntriesR (p : Pose ℚ) (w : Fin 2 → ℚ) : HEntries :=
  let e := hEntries p w
  ⟨round13v e.m2tw, round13v e.m2θtw, round13v e.m2φtw,
   round13v e.m2θθtw, round13v e.m2θφtw, round13v e.m2φφtw⟩

@[inline] private def fastH (entries : HEntries) (εθ εφ : ℚ) (kappaTerm : ℚ) (P : Fin 3 → ℚ) : ℚ :=
  entries.m2tw ⬝ᵥ P + εθ * |entries.m2θtw ⬝ᵥ P| + εφ * |entries.m2φtw ⬝ᵥ P|
    + 1 / 2 * (εθ^2 * |entries.m2θθtw ⬝ᵥ P| + 2 * (εθ * εφ) * |entries.m2θφtw ⬝ᵥ P|
        + εφ^2 * |entries.m2φφtw ⬝ᵥ P|)
    + (εθ + εφ)^3 / 6 + kappaTerm

/-- Pre-computed `(M_combined)ᵀ·w` 3-vectors for the nine matrix chains in
`Gℚ` (`R·M₁`, `R'·M₁`, `R·M₁θ`, `R·M₁φ`, `R'·M₁θ`, `R'·M₁φ`, `R·M₁θθ`,
`R·M₁θφ`, `R·M₁φφ`). With these, each chain in `Gℚ` collapses to a single
3-element dot product against `S`. -/
private structure GEntries : Type where
  m1RTw    : Fin 3 → ℚ  -- (R · M₁)ᵀ · w   for `p.innerℚ S ⬝ᵥ w`
  m1R'Tw   : Fin 3 → ℚ  -- (R' · M₁)ᵀ · w  for `p.rotR'ℚ (p.rotM₁ℚ S) ⬝ᵥ w`
  m1θRTw   : Fin 3 → ℚ  -- (R · M₁θ)ᵀ · w  for `p.rotRℚ (p.rotM₁θℚ S) ⬝ᵥ w`
  m1φRTw   : Fin 3 → ℚ  -- (R · M₁φ)ᵀ · w  for `p.rotRℚ (p.rotM₁φℚ S) ⬝ᵥ w`
  m1θR'Tw  : Fin 3 → ℚ  -- (R' · M₁θ)ᵀ · w for `p.rotR'ℚ (p.rotM₁θℚ S) ⬝ᵥ w`
  m1φR'Tw  : Fin 3 → ℚ  -- (R' · M₁φ)ᵀ · w for `p.rotR'ℚ (p.rotM₁φℚ S) ⬝ᵥ w`
  m1θθRTw  : Fin 3 → ℚ  -- (R · M₁θθ)ᵀ · w for `p.rotRℚ (p.rotM₁θθℚ S) ⬝ᵥ w`
  m1θφRTw  : Fin 3 → ℚ  -- (R · M₁θφ)ᵀ · w for `p.rotRℚ (p.rotM₁θφℚ S) ⬝ᵥ w`
  m1φφRTw  : Fin 3 → ℚ  -- (R · M₁φφ)ᵀ · w for `p.rotRℚ (p.rotM₁φφℚ S) ⬝ᵥ w`

@[inline] private def gEntries (p : Pose ℚ) (w : Fin 2 → ℚ) : GEntries :=
  let st1 := (RationalApprox.sinNum13 p.θ₁ : ℚ) / 10 ^ 13
  let ct1 := (RationalApprox.cosNum13 p.θ₁ : ℚ) / 10 ^ 13
  let sp1 := (RationalApprox.sinNum13 p.φ₁ : ℚ) / 10 ^ 13
  let cp1 := (RationalApprox.cosNum13 p.φ₁ : ℚ) / 10 ^ 13
  let sa  := (RationalApprox.sinNum13 p.α : ℚ) / 10 ^ 13
  let ca  := (RationalApprox.cosNum13 p.α : ℚ) / 10 ^ 13
  let w0 := w 0
  let w1 := w 1
  -- Rᵀ · w = (ca·w0 + sa·w1, -sa·w0 + ca·w1)
  let u0  := ca * w0 + sa * w1
  let u1  := -sa * w0 + ca * w1
  -- R'ᵀ · w = (-sa·w0 + ca·w1, -ca·w0 + (-sa)·w1)
  let up0 := -sa * w0 + ca * w1
  let up1 := -ca * w0 + (-sa) * w1
  -- M₁ᵀ · u: uses (M₁[j][i])
  -- M₁   = [[-st1, ct1, 0], [-ct1*cp1, -st1*cp1, sp1]]
  -- M₁θ  = [[-ct1, -st1, 0], [st1*cp1, -ct1*cp1, 0]]
  -- M₁φ  = [[0, 0, 0], [ct1*sp1, st1*sp1, cp1]]
  -- M₁θθ = [[st1, -ct1, 0], [ct1*cp1, st1*cp1, 0]]
  -- M₁θφ = [[0, 0, 0], [-st1*sp1, ct1*sp1, 0]]
  -- M₁φφ = [[0, 0, 0], [ct1*cp1, st1*cp1, -sp1]]
  ⟨ ![-st1 * u0 + (-ct1 * cp1) * u1,
       ct1 * u0 + (-st1 * cp1) * u1,
       sp1 * u1],
    -- M₁ᵀ · u'
    ![-st1 * up0 + (-ct1 * cp1) * up1,
       ct1 * up0 + (-st1 * cp1) * up1,
       sp1 * up1],
    -- M₁θᵀ · u
    ![-ct1 * u0 + (st1 * cp1) * u1,
      -st1 * u0 + (-ct1 * cp1) * u1,
       0],
    -- M₁φᵀ · u
    ![(ct1 * sp1) * u1,
      (st1 * sp1) * u1,
       cp1 * u1],
    -- M₁θᵀ · u'
    ![-ct1 * up0 + (st1 * cp1) * up1,
      -st1 * up0 + (-ct1 * cp1) * up1,
       0],
    -- M₁φᵀ · u'
    ![(ct1 * sp1) * up1,
      (st1 * sp1) * up1,
       cp1 * up1],
    -- M₁θθᵀ · u
    ![ st1 * u0 + (ct1 * cp1) * u1,
      -ct1 * u0 + (st1 * cp1) * u1,
       0],
    -- M₁θφᵀ · u
    ![(-st1 * sp1) * u1,
      (ct1 * sp1) * u1,
       0],
    -- M₁φφᵀ · u
    ![(ct1 * cp1) * u1,
      (st1 * cp1) * u1,
      -sp1 * u1] ⟩

/-- `gEntries` with each hoisted vector rounded down to multiples of `10⁻¹³`.
(Each component is read at most twice per row by `fastG`.) -/
@[inline] private def gEntriesR (p : Pose ℚ) (w : Fin 2 → ℚ) : GEntries :=
  let e := gEntries p w
  ⟨round13v e.m1RTw, round13v e.m1R'Tw, round13v e.m1θRTw, round13v e.m1φRTw,
   round13v e.m1θR'Tw, round13v e.m1φR'Tw,
   round13v e.m1θθRTw, round13v e.m1θφRTw, round13v e.m1φφRTw⟩

/-- Shared proof for the fifteen `*_dot_eq` identities below: unfold the pose
matrices and both hoisted-entry structures to scalars, then close with `ring`. -/
local macro "dot_eq_tac" : tactic =>
  `(tactic| (
    simp [RationalApprox.sinNum13_div_eq, RationalApprox.cosNum13_div_eq,
      hEntries, gEntries, Pose.innerℚ, Pose.rotRℚ, Pose.rotR'ℚ,
      Pose.rotM₁ℚ, Pose.rotM₁θℚ, Pose.rotM₁φℚ, Pose.rotM₁θθℚ, Pose.rotM₁θφℚ, Pose.rotM₁φφℚ,
      Pose.rotM₂ℚ, Pose.rotM₂θℚ, Pose.rotM₂φℚ, Pose.rotM₂θθℚ, Pose.rotM₂θφℚ, Pose.rotM₂φφℚ,
      RationalApprox.rotRℚ, RationalApprox.rotR'ℚ, RationalApprox.rotMℚ,
      RationalApprox.rotMθℚ, RationalApprox.rotMφℚ, RationalApprox.rotMθθℚ,
      RationalApprox.rotMθφℚ, RationalApprox.rotMφφℚ,
      RationalApprox.rotRℚ_mat, RationalApprox.rotR'ℚ_mat, RationalApprox.rotMℚ_mat,
      RationalApprox.rotMθℚ_mat, RationalApprox.rotMφℚ_mat, RationalApprox.rotMθθℚ_mat,
      RationalApprox.rotMθφℚ_mat, RationalApprox.rotMφφℚ_mat,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring))

private lemma m2tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2tw ⬝ᵥ P = p.rotM₂ℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2θtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θtw ⬝ᵥ P = p.rotM₂θℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2φtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2φtw ⬝ᵥ P = p.rotM₂φℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2θθtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θθtw ⬝ᵥ P = p.rotM₂θθℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2θφtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θφtw ⬝ᵥ P = p.rotM₂θφℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2φφtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2φφtw ⬝ᵥ P = p.rotM₂φφℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m1RTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1RTw ⬝ᵥ S = p.innerℚ S ⬝ᵥ w := by dot_eq_tac

private lemma m1R'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1R'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁ℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1φRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁φℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θR'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θR'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁θℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1φR'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φR'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁φℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θθRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θθRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θθℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θφRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θφRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θφℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1φφRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φφRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁φφℚ S) ⬝ᵥ w := by dot_eq_tac

@[inline] private def fastG (entries : GEntries) (εα εθ εφ : ℚ) (S : Fin 3 → ℚ) : ℚ :=
  entries.m1RTw ⬝ᵥ S -
   (εα * |entries.m1R'Tw ⬝ᵥ S| + εθ * |entries.m1θRTw ⬝ᵥ S| + εφ * |entries.m1φRTw ⬝ᵥ S|
     + 1 / 2 * (εα^2 * |entries.m1RTw ⬝ᵥ S|
         + 2 * (εα * εθ) * |entries.m1θR'Tw ⬝ᵥ S| + 2 * (εα * εφ) * |entries.m1φR'Tw ⬝ᵥ S|
         + εθ^2 * |entries.m1θθRTw ⬝ᵥ S| + 2 * (εθ * εφ) * |entries.m1θφRTw ⬝ᵥ S|
         + εφ^2 * |entries.m1φφRTw ⬝ᵥ S|)
     + (εα + εθ + εφ)^3 / 6
     + 4 * κℚ * (1 + (εα + εθ + εφ) + (εα + εθ + εφ)^2 / 2))

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
  d0 : ℚ
  d1 : ℚ
  d2 : ℚ
  e0 : ℚ
  e1 : ℚ
  e2 : ℚ
  f0 : ℚ
  f1 : ℚ
  f2 : ℚ

@[inline] private def HEntries.scalars (e : HEntries) : HScalars :=
  ⟨e.m2tw 0, e.m2tw 1, e.m2tw 2,
   e.m2θtw 0, e.m2θtw 1, e.m2θtw 2,
   e.m2φtw 0, e.m2φtw 1, e.m2φtw 2,
   e.m2θθtw 0, e.m2θθtw 1, e.m2θθtw 2,
   e.m2θφtw 0, e.m2θφtw 1, e.m2θφtw 2,
   e.m2φφtw 0, e.m2φφtw 1, e.m2φφtw 2⟩

/-- `fastH` on precomputed scalars, with the dot products written out. Takes
the vertex coordinates as scalars so each is read (a `ℚ` division for the
table's vertex functions) only once per vertex. -/
@[inline] private def fastHs (e : HScalars) (εθ εφ : ℚ) (kappaTerm : ℚ) (p0 p1 p2 : ℚ) : ℚ :=
  e.a0 * p0 + e.a1 * p1 + e.a2 * p2
    + εθ * |e.b0 * p0 + e.b1 * p1 + e.b2 * p2| + εφ * |e.c0 * p0 + e.c1 * p1 + e.c2 * p2|
    + 1 / 2 * (εθ^2 * |e.d0 * p0 + e.d1 * p1 + e.d2 * p2|
        + 2 * (εθ * εφ) * |e.e0 * p0 + e.e1 * p1 + e.e2 * p2|
        + εφ^2 * |e.f0 * p0 + e.f1 * p1 + e.f2 * p2|)
    + (εθ + εφ)^3 / 6 + kappaTerm

private lemma fastHs_scalars_eq (e : HEntries) (εθ εφ kt : ℚ) (P : Fin 3 → ℚ) :
    fastHs e.scalars εθ εφ kt (P 0) (P 1) (P 2) = fastH e εθ εφ kt P := by
  simp only [fastHs, HEntries.scalars, fastH, dotProduct, Fin.sum_univ_three]

/-! #### Three-tier `H` test

For all but the few near-binding vertices `P`, the margin `g − H(P)` dwarfs
everything past the zeroth-order dot product, so per-pose ∞-norm bounds on
the first- and second-order vectors (`foBound`/`soBound`) let the common
case decide with the single `a`-dot product plus one multiply
(`cheapestHs`); the vertices that fail fall back to the three-dot `cheapHs`
(second-order group still bounded by `soBound`), and only the near-binding
ones run the exact six-dot `fastHs`. Since
`cheapestHs ≥ cheapHs ≥ fastHs` pointwise, the tiered test decides exactly
`g > fastHs`. -/

/-- Upper bound for `fastHs` that replaces the three second-order dot
products by the precomputed scalar `soBound * (|p0| + |p1| + |p2|)`. -/
@[inline] private def cheapHs (e : HScalars) (εθ εφ kappaTerm soBound p0 p1 p2 : ℚ) : ℚ :=
  e.a0 * p0 + e.a1 * p1 + e.a2 * p2
    + εθ * |e.b0 * p0 + e.b1 * p1 + e.b2 * p2| + εφ * |e.c0 * p0 + e.c1 * p1 + e.c2 * p2|
    + soBound * (|p0| + |p1| + |p2|)
    + (εθ + εφ)^3 / 6 + kappaTerm

/-- The per-pose scalar for `cheapHs`: the `(εθ², 2εθεφ, εφ²)/2`-weighted
∞-norms of the three second-order vectors. -/
@[inline] private def soBound (e : HScalars) (εθ εφ : ℚ) : ℚ :=
  1 / 2 * (εθ^2 * max |e.d0| (max |e.d1| |e.d2|)
    + 2 * (εθ * εφ) * max |e.e0| (max |e.e1| |e.e2|)
    + εφ^2 * max |e.f0| (max |e.f1| |e.f2|))

/-- The first-order half of the per-pose scalar for `cheapestHs`: the
`(εθ, εφ)`-weighted ∞-norms of the two first-order vectors. -/
@[inline] private def foBound (e : HScalars) (εθ εφ : ℚ) : ℚ :=
  εθ * max |e.b0| (max |e.b1| |e.b2|) + εφ * max |e.c0| (max |e.c1| |e.c2|)

/-- Tier-0 upper bound for `fastHs`: everything past the zeroth-order dot
product is replaced by the two per-pose scalars
`fsBound = foBound + soBound` and `kappaRem = (εθ+εφ)³/6 + kappaTerm`, so
each vertex costs one dot product and one multiply. -/
@[inline] private def cheapestHs (e : HScalars) (fsBound kappaRem p0 p1 p2 : ℚ) : ℚ :=
  e.a0 * p0 + e.a1 * p1 + e.a2 * p2 + fsBound * (|p0| + |p1| + |p2|) + kappaRem

private lemma abs_dot3_le (d0 d1 d2 p0 p1 p2 : ℚ) :
    |d0 * p0 + d1 * p1 + d2 * p2| ≤
      max |d0| (max |d1| |d2|) * (|p0| + |p1| + |p2|) := by
  have h0 : |d0| ≤ max |d0| (max |d1| |d2|) := le_max_left _ _
  have h1 : |d1| ≤ max |d0| (max |d1| |d2|) := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : |d2| ≤ max |d0| (max |d1| |d2|) := le_trans (le_max_right _ _) (le_max_right _ _)
  calc |d0 * p0 + d1 * p1 + d2 * p2|
      ≤ |d0 * p0| + |d1 * p1| + |d2 * p2| := abs_add_three _ _ _
    _ = |d0| * |p0| + |d1| * |p1| + |d2| * |p2| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ max |d0| (max |d1| |d2|) * |p0| + max |d0| (max |d1| |d2|) * |p1|
        + max |d0| (max |d1| |d2|) * |p2| := by
          gcongr
    _ = max |d0| (max |d1| |d2|) * (|p0| + |p1| + |p2|) := by ring

private lemma fastHs_le_cheapHs {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (e : HScalars) (kt p0 p1 p2 : ℚ) :
    fastHs e εθ εφ kt p0 p1 p2 ≤ cheapHs e εθ εφ kt (soBound e εθ εφ) p0 p1 p2 := by
  unfold fastHs cheapHs soBound
  have hd := mul_le_mul_of_nonneg_left (abs_dot3_le e.d0 e.d1 e.d2 p0 p1 p2)
    (mul_nonneg hεθ hεθ)
  have he := mul_le_mul_of_nonneg_left (abs_dot3_le e.e0 e.e1 e.e2 p0 p1 p2)
    (mul_nonneg hεθ hεφ)
  have hf := mul_le_mul_of_nonneg_left (abs_dot3_le e.f0 e.f1 e.f2 p0 p1 p2)
    (mul_nonneg hεφ hεφ)
  linarith [hd, he, hf]

private lemma fastHs_le_cheapestHs {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (e : HScalars) (kt p0 p1 p2 : ℚ) :
    fastHs e εθ εφ kt p0 p1 p2 ≤
      cheapestHs e (foBound e εθ εφ + soBound e εθ εφ) ((εθ + εφ)^3 / 6 + kt) p0 p1 p2 := by
  unfold fastHs cheapestHs foBound soBound
  have hb := mul_le_mul_of_nonneg_left (abs_dot3_le e.b0 e.b1 e.b2 p0 p1 p2) hεθ
  have hc := mul_le_mul_of_nonneg_left (abs_dot3_le e.c0 e.c1 e.c2 p0 p1 p2) hεφ
  have hd := mul_le_mul_of_nonneg_left (abs_dot3_le e.d0 e.d1 e.d2 p0 p1 p2)
    (mul_nonneg hεθ hεθ)
  have he := mul_le_mul_of_nonneg_left (abs_dot3_le e.e0 e.e1 e.e2 p0 p1 p2)
    (mul_nonneg hεθ hεφ)
  have hf := mul_le_mul_of_nonneg_left (abs_dot3_le e.f0 e.f1 e.f2 p0 p1 p2)
    (mul_nonneg hεφ hεφ)
  linarith [hb, hc, hd, he, hf]

/-- One vertex of the three-tier test: try `cheapestHs` (one dot product),
then `cheapHs` (three), and fall back to the exact `fastHs` (six) only if
both fail. `Bool.or` is short-circuiting, so the later tiers are not
evaluated when an earlier test passes. -/
@[inline] private def tieredHs_lt (e : HScalars) (εθ εφ kappaTerm soB fsB kR g p0 p1 p2 : ℚ) :
    Bool :=
  decide (g > cheapestHs e fsB kR p0 p1 p2) ||
  decide (g > cheapHs e εθ εφ kappaTerm soB p0 p1 p2) ||
  decide (g > fastHs e εθ εφ kappaTerm p0 p1 p2)

private lemma tieredHs_lt_iff {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (e : HScalars) (kt g p0 p1 p2 : ℚ) :
    tieredHs_lt e εθ εφ kt (soBound e εθ εφ) (foBound e εθ εφ + soBound e εθ εφ)
      ((εθ + εφ)^3 / 6 + kt) g p0 p1 p2 = true ↔
      g > fastHs e εθ εφ kt p0 p1 p2 := by
  simp only [tieredHs_lt, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨fun h => ?_, fun h => Or.inr h⟩
  obtain (h | h) | h := h
  · exact lt_of_le_of_lt (fastHs_le_cheapestHs hεθ hεφ e kt p0 p1 p2) h
  · exact lt_of_le_of_lt (fastHs_le_cheapHs hεθ hεφ e kt p0 p1 p2) h
  · exact h

end Gℚ_gt_maxHℚ

open Gℚ_gt_maxHℚ in
/--
A measure of how far an inner-shadow vertex S can "stick out".

Second-order anisotropic certificate: the per-axis radii `εα`, `εθ`, `εφ`
weight the first partials, the exact second partials at the center (with
multiplicities from the symmetric 3×3 table), and an `(εα+εθ+εφ)³/6`
Lagrange remainder. The nine hoisted `(R·M₁)ᵀ·w`-style 3-vectors are rounded
down to multiples of `10⁻¹³` (`gEntriesR`); with `E = εα+εθ+εφ`, the
`4κℚ(1+E+E²/2)` term absorbs the `sinℚ`/`cosℚ` approximation error and this
rounding for each chain at its weight (see `Gℚ_le_G`). On the diagonal
`εα = εθ = εφ = ε` this recovers the isotropic remainder `9ε³/2` and slack
`4κℚ(1+3ε+(9/2)ε²)`.
-/
def Gℚ (p : Pose ℚ) (εα εθ εφ : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) : ℚ :=
  fastG (gEntriesR p w) εα εθ εφ S

open Gℚ_gt_maxHℚ in
/--
A measure of how far an outer-shadow vertex P can "reach" along w.

Second-order anisotropic certificate with per-axis radii `εθ`, `εφ` and
Lagrange remainder `(εθ+εφ)³/6`. The six hoisted `M₂ᵀ·w`-style 3-vectors are
rounded down to multiples of `10⁻¹³` (`hEntriesR`); with `E = εθ+εφ`, the
`3κℚ(1+E+E²/2)` term absorbs both the `sinℚ`/`cosℚ` approximation error and
this rounding (see `H_le_Hℚ`). On the diagonal `εθ = εφ = ε` this recovers
the isotropic remainder `4ε³/3` and slack `3κℚ(1+2ε+2ε²)`.
-/
def Hℚ (p : Pose ℚ) (εθ εφ : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) : ℚ :=
  fastH (hEntriesR p w) εθ εφ (3 * κℚ * (1 + (εθ + εφ) + (εθ + εφ)^2 / 2)) P

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
def maxHℚ {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (εθ εφ : ℚ) (w : Fin 2 → ℚ) : ℚ :=
  Finset.image (Hℚ p εθ εφ w ∘ poly.v) Finset.univ  |>.max' <| by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr ne

private lemma fastG_eq_Gℚ (p : Pose ℚ) (εα εθ εφ : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ.fastG (Gℚ_gt_maxHℚ.gEntriesR p w) εα εθ εφ S = Gℚ p εα εθ εφ S w := rfl

private lemma fastH_eq_Hℚ (p : Pose ℚ) (εθ εφ : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    Gℚ_gt_maxHℚ.fastH (Gℚ_gt_maxHℚ.hEntriesR p w) εθ εφ
      (3 * κℚ * (1 + (εθ + εφ) + (εθ + εφ)^2 / 2)) P = Hℚ p εθ εφ w P :=
  rfl

open Gℚ_gt_maxHℚ in
/-- Bool-valued `Gℚ > maxHℚ` check that hoists the trig partial sums and the
rounded `Mᵀ·w` 3-vectors to per-pose work for both `Gℚ` and `Hℚ`; the
`∀ P ∈ poly.v` loop then only does small-denominator dot products, and the
three-tier `tieredHs_lt` decides all but the near-binding vertices with the
single zeroth-order dot product alone. -/
def Gℚ_gt_maxHℚ_check {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (S : Fin 3 → ℚ)
    (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) : Bool :=
  let hscalars := (hEntriesR p w).scalars
  let g := fastG (gEntriesR p w) εα εθ₁ εφ₁ S
  let kappaTerm := 3 * κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂)^2 / 2)
  let soB := soBound hscalars εθ₂ εφ₂
  let fsB := foBound hscalars εθ₂ εφ₂ + soB
  let kR := (εθ₂ + εφ₂)^3 / 6 + kappaTerm
  decide <| ∀ k : ι,
    tieredHs_lt hscalars εθ₂ εφ₂ kappaTerm soB fsB kR g
      (poly.v k 0) (poly.v k 1) (poly.v k 2) = true

theorem Gℚ_gt_maxHℚ_check_iff {ι : Type} [Fintype ι] [DecidableEq ι] [ne : Nonempty ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ : ℚ) {εθ₂ εφ₂ : ℚ} (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (S : Fin 3 → ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ_check p εα εθ₁ εφ₁ εθ₂ εφ₂ S poly w = true ↔
      Gℚ p εα εθ₁ εφ₁ S w > maxHℚ p poly εθ₂ εφ₂ w := by
  unfold Gℚ_gt_maxHℚ_check maxHℚ
  simp only [decide_eq_true_eq, Gℚ_gt_maxHℚ.tieredHs_lt_iff hεθ₂ hεφ₂]
  rw [fastG_eq_Gℚ]
  constructor
  · intro hAll
    show (Finset.image (Hℚ p εθ₂ εφ₂ w ∘ poly.v) Finset.univ).max' _ < Gℚ p εα εθ₁ εφ₁ S w
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
A compact way of saying "the pose satisfies the rational global theorem precondition at
per-axis widths `εα εθ₁ εφ₁ εθ₂ εφ₂`".
We require the existence of some inner-shadow vertex S from the polyhedron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure RationalGlobalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_) (p : Pose ℚ)
    (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) : Type where
  j : ι
  p_in_4 : p ∈ fourInterval ℚ
  w : Fin 2 → ℚ
  w_unit : ‖toR2 w‖ = 1
  exceeds : Gℚ p εα εθ₁ εφ₁ (poly_.v j) w > maxHℚ p poly_ εθ₂ εφ₂ w

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
`bounds_kappa_M`-style base bound (about the matrix form `d` of the hoisted
dot product, see the `*_dot_eq` lemmas) plus the rounding perturbation is
≤ `3κ`. -/
private lemma norm_sub_round13v_dot_le₃ {x : ℝ} {v P_ : Fin 3 → ℚ} {d : ℚ}
    (hdot : v ⬝ᵥ P_ = d) (hbase : ‖x - (d : ℝ)‖ ≤ 2 * κ + κ ^ 2)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
  (norm_sub_round13v_dot_le (hdot ▸ hbase) hsum).trans (by unfold κ; norm_num)

/-- `norm_sub_round13v_dot_le` specialised to the `G`-side budget: a
`bounds_kappa_RM`-style base bound plus the rounding perturbation is ≤ `4κ`. -/
private lemma norm_sub_round13v_dot_le₄ {x : ℝ} {v P_ : Fin 3 → ℚ} {d : ℚ}
    (hdot : v ⬝ᵥ P_ = d) (hbase : ‖x - (d : ℝ)‖ ≤ 3 * κ + 3 * κ ^ 2 + κ ^ 3)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
  (norm_sub_round13v_dot_le (hdot ▸ hbase) hsum).trans (by unfold κ; norm_num)

open Gℚ_gt_maxHℚ in
private lemma Gℚ_le_G {p_ : Pose ℚ} {εα εθ εφ : ℚ}
    (hεα : 0 ≤ εα) (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    {S : ℝ³} {S_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hS : ‖S‖ ≤ 1) (hS_approx : ‖S - toR3 S_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains p_) :
    Gℚ p_ εα εθ εφ S_ w ≤ GlobalTheorem.G p_.toReal εα εθ εφ S (toR2 w) := by
  set pbar := p_.toReal with hpbar
  have hsum := sum_abs_le_of_approx hS hS_approx
  let α4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.α, hp.αBound⟩
  let θ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.θ₁, hp.θ₁Bound⟩
  let φ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.φ₁, hp.φ₁Bound⟩
  unfold Gℚ fastG GlobalTheorem.G
  rw [show pbar.inner S = pbar.rotR (pbar.rotM₁ S) by rw [Pose.inner_eq_RM]; rfl]
  have h_RM : ‖⟪pbar.rotR (pbar.rotM₁ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1RTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1RTw_dot_eq p_ w S_)
      (bounds_kappa_RM (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_R'M : ‖⟪pbar.rotR' (pbar.rotM₁ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1R'Tw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1R'Tw_dot_eq p_ w S_)
      (bounds_kappa_R'M (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMθ : ‖⟪pbar.rotR (pbar.rotM₁θ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θRTw_dot_eq p_ w S_)
      (bounds_kappa_RMθ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMφ : ‖⟪pbar.rotR (pbar.rotM₁φ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1φRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1φRTw_dot_eq p_ w S_)
      (bounds_kappa_RMφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_R'Mθ : ‖⟪pbar.rotR' (pbar.rotM₁θ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θR'Tw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θR'Tw_dot_eq p_ w S_)
      (bounds_kappa_R'Mθ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_R'Mφ : ‖⟪pbar.rotR' (pbar.rotM₁φ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1φR'Tw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1φR'Tw_dot_eq p_ w S_)
      (bounds_kappa_R'Mφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMθθ : ‖⟪pbar.rotR (pbar.rotM₁θθ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θθRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θθRTw_dot_eq p_ w S_)
      (bounds_kappa_RMθθ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMθφ : ‖⟪pbar.rotR (pbar.rotM₁θφ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θφRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θφRTw_dot_eq p_ w S_)
      (bounds_kappa_RMθφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMφφ : ‖⟪pbar.rotR (pbar.rotM₁φφ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1φφRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1φφRTw_dot_eq p_ w S_)
      (bounds_kappa_RMφφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have hi_le : (((gEntriesR p_ w).m1RTw ⬝ᵥ S_ : ℚ) : ℝ) ≤
               ⟪pbar.rotR (pbar.rotM₁ S), toR2 w⟫ + 4 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_RM; rw [abs_le] at this
    linarith [this.1]
  have hRM_abs := abs_le_abs_add_of_norm_sub_le h_RM
  have hR'_abs := abs_le_abs_add_of_norm_sub_le h_R'M
  have hRθ_abs := abs_le_abs_add_of_norm_sub_le h_RMθ
  have hRφ_abs := abs_le_abs_add_of_norm_sub_le h_RMφ
  have hR'θ_abs := abs_le_abs_add_of_norm_sub_le h_R'Mθ
  have hR'φ_abs := abs_le_abs_add_of_norm_sub_le h_R'Mφ
  have hθθ_abs := abs_le_abs_add_of_norm_sub_le h_RMθθ
  have hθφ_abs := abs_le_abs_add_of_norm_sub_le h_RMθφ
  have hφφ_abs := abs_le_abs_add_of_norm_sub_le h_RMφφ
  have h_κ : ((κℚ : ℚ) : ℝ) = κ := cast_κℚ
  have hεα_real : (0 : ℝ) ≤ εα := mod_cast hεα
  have hεθ_real : (0 : ℝ) ≤ εθ := mod_cast hεθ
  have hεφ_real : (0 : ℝ) ≤ εφ := mod_cast hεφ
  push_cast
  rw [h_κ]
  -- Each weighted `|real dot|` is at most the same weight times
  -- `|rational dot| + 4κ`; with `E = εα+εθ+εφ`, the accumulated per-term
  -- `4κ`-weights sum to exactly `4κ(E + E²/2)`, so together with the `4κ`
  -- from `hi_le` the `4κ(1 + E + E²/2)` slack closes the gap.
  have hfoα := mul_le_mul_of_nonneg_left hR'_abs hεα_real
  have hfoθ := mul_le_mul_of_nonneg_left hRθ_abs hεθ_real
  have hfoφ := mul_le_mul_of_nonneg_left hRφ_abs hεφ_real
  have hsoαα := mul_le_mul_of_nonneg_left hRM_abs (mul_nonneg hεα_real hεα_real)
  have hsoαθ := mul_le_mul_of_nonneg_left hR'θ_abs (mul_nonneg hεα_real hεθ_real)
  have hsoαφ := mul_le_mul_of_nonneg_left hR'φ_abs (mul_nonneg hεα_real hεφ_real)
  have hsoθθ := mul_le_mul_of_nonneg_left hθθ_abs (mul_nonneg hεθ_real hεθ_real)
  have hsoθφ := mul_le_mul_of_nonneg_left hθφ_abs (mul_nonneg hεθ_real hεφ_real)
  have hsoφφ := mul_le_mul_of_nonneg_left hφφ_abs (mul_nonneg hεφ_real hεφ_real)
  linarith [hi_le, hfoα, hfoθ, hfoφ, hsoαα, hsoαθ, hsoαφ, hsoθθ, hsoθφ, hsoφφ]

open Gℚ_gt_maxHℚ in
private lemma H_le_Hℚ {p_ : Pose ℚ} {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    {P : ℝ³} {P_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains p_) :
    GlobalTheorem.H p_.toReal εθ εφ (toR2 w) P ≤ Hℚ p_ εθ εφ w P_ := by
  set pbar := p_.toReal with hpbar
  have hsum := sum_abs_le_of_approx hP hP_approx
  let θ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.θ₂, hp.θ₂Bound⟩
  let φ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.φ₂, hp.φ₂Bound⟩
  unfold GlobalTheorem.H Hℚ fastH
  have h_M : ‖⟪pbar.rotM₂ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2tw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2tw_dot_eq p_ w P_)
      (bounds_kappa_M (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mθ : ‖⟪pbar.rotM₂θ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2θtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2θtw_dot_eq p_ w P_)
      (bounds_kappa_Mθ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mφ : ‖⟪pbar.rotM₂φ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2φtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2φtw_dot_eq p_ w P_)
      (bounds_kappa_Mφ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mθθ : ‖⟪pbar.rotM₂θθ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2θθtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2θθtw_dot_eq p_ w P_)
      (bounds_kappa_Mθθ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mθφ : ‖⟪pbar.rotM₂θφ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2θφtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2θφtw_dot_eq p_ w P_)
      (bounds_kappa_Mθφ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mφφ : ‖⟪pbar.rotM₂φφ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2φφtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2φφtw_dot_eq p_ w P_)
      (bounds_kappa_Mφφ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have hm_le : ⟪pbar.rotM₂ P, toR2 w⟫ ≤
               (((hEntriesR p_ w).m2tw ⬝ᵥ P_ : ℚ) : ℝ) + 3 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_M; rw [abs_le] at this
    linarith [this.2]
  have hθ_abs := abs_le_abs_add_of_norm_sub_le h_Mθ
  have hφ_abs := abs_le_abs_add_of_norm_sub_le h_Mφ
  have hθθ_abs := abs_le_abs_add_of_norm_sub_le h_Mθθ
  have hθφ_abs := abs_le_abs_add_of_norm_sub_le h_Mθφ
  have hφφ_abs := abs_le_abs_add_of_norm_sub_le h_Mφφ
  have h_κ : ((κℚ : ℚ) : ℝ) = κ := cast_κℚ
  have hεθ_real : (0 : ℝ) ≤ εθ := mod_cast hεθ
  have hεφ_real : (0 : ℝ) ≤ εφ := mod_cast hεφ
  push_cast
  rw [h_κ]
  -- Each weighted `|real dot|` is at most the same weight times
  -- `|rational dot| + 3κ`; with `E = εθ+εφ`, the accumulated per-term
  -- `3κ`-weights sum to exactly `3κ(E + E²/2)`, so together with the `3κ`
  -- from `hm_le` the `3κ(1 + E + E²/2)` slack closes the gap.
  have hfoθ := mul_le_mul_of_nonneg_left hθ_abs hεθ_real
  have hfoφ := mul_le_mul_of_nonneg_left hφ_abs hεφ_real
  have hsoθθ := mul_le_mul_of_nonneg_left hθθ_abs (mul_nonneg hεθ_real hεθ_real)
  have hsoθφ := mul_le_mul_of_nonneg_left hθφ_abs (mul_nonneg hεθ_real hεφ_real)
  have hsoφφ := mul_le_mul_of_nonneg_left hφφ_abs (mul_nonneg hεφ_real hεφ_real)
  linarith [hm_le, hfoθ, hfoφ, hsoθθ, hsoθφ, hsoφφ]

/--
[SY25] Theorem 43, with per-axis widths and a box conclusion in place of the
closed ball.
-/
theorem rational_global {ι : Type} [Fintype ι] [Nonempty ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁) (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_)
    (pc : RationalGlobalTheoremPrecondition poly poly_ happrox p εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ¬ ∃ q, Pose.near p.toReal (εα : ℝ) (εθ₁ : ℝ) (εφ₁ : ℝ) (εθ₂ : ℝ) (εφ₂ : ℝ) q ∧
      RupertPose q poly.hull := by
  set pbar := p.toReal
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
  have h_maxH_le : GlobalTheorem.maxH pbar poly εθ₂ εφ₂ (toR2 pc.w) ≤
      ((maxHℚ p poly_ εθ₂ εφ₂ pc.w : ℚ) : ℝ) := by
    unfold GlobalTheorem.maxH
    apply Finset.max'_le
    simp only [Function.comp, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨k, rfl⟩
    let k' := happrox.bijection k
    have hk_norm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
    have hk_approx : ‖poly.vertices.v k - poly_.toReal.v k'‖ ≤ κ := happrox.approx k
    have h_le_Hℚ : GlobalTheorem.H pbar εθ₂ εφ₂ (toR2 pc.w) (poly.vertices.v k) ≤
                    Hℚ p εθ₂ εφ₂ pc.w (poly_.v k') :=
      H_le_Hℚ hεθ₂ hεφ₂ hk_norm
        (show ‖poly.vertices.v k - toR3 (poly_.v k')‖ ≤ κ from hk_approx)
        pc.w_unit pc.p_in_4
    have h_le_max : Hℚ p εθ₂ εφ₂ pc.w (poly_.v k') ≤ maxHℚ p poly_ εθ₂ εφ₂ pc.w := by
      unfold maxHℚ
      have : (Hℚ p εθ₂ εφ₂ pc.w ∘ poly_.v) k' ∈
              Finset.image (Hℚ p εθ₂ εφ₂ pc.w ∘ poly_.v) Finset.univ :=
        Finset.mem_image_of_mem _ (Finset.mem_univ k')
      exact Finset.le_max' _ _ this
    have h_le_max_real : ((Hℚ p εθ₂ εφ₂ pc.w (poly_.v k') : ℚ) : ℝ) ≤
        ((maxHℚ p poly_ εθ₂ εφ₂ pc.w : ℚ) : ℝ) :=
      mod_cast h_le_max
    linarith [h_le_Hℚ, h_le_max_real]
  -- Step 3: Build the box precondition and apply global_theorem directly.
  rintro ⟨q, hq_near, hq_rupert⟩
  exact GlobalTheorem.global_theorem pbar εα εθ₁ εφ₁ εθ₂ εφ₂
    (Rat.cast_nonneg.mpr hεα) (Rat.cast_nonneg.mpr hεθ₁) (Rat.cast_nonneg.mpr hεφ₁)
    (Rat.cast_nonneg.mpr hεθ₂) (Rat.cast_nonneg.mpr hεφ₂) poly {
    Si := i
    w := toR2 pc.w
    w_unit := pc.w_unit
    exceeds := by
      have hG_le := Gℚ_le_G hεα hεθ₁ hεφ₁ hS_norm hS_approx pc.w_unit pc.p_in_4
      have hexceeds_real : ((Gℚ p εα εθ₁ εφ₁ (poly_.v pc.j) pc.w : ℚ) : ℝ) >
                            ((maxHℚ p poly_ εθ₂ εφ₂ pc.w : ℚ) : ℝ) := mod_cast pc.exceeds
      linarith [hG_le, hexceeds_real, h_maxH_le]
  } ⟨q, hq_near, hq_rupert⟩


/-! ## Integer core of the per-vertex tier test -/

namespace Gℚ_gt_maxHℚ

private lemma abs_intCast_div (n D : ℤ) (hD : (0:ℤ) < D) :
    |(n : ℚ) / (D : ℚ)| = ((|n| : ℤ) : ℚ) / ((D : ℤ) : ℚ) := by
  rw [abs_div, abs_of_pos (by exact_mod_cast hD : (0:ℚ) < (D : ℚ))]
  push_cast
  ring_nf

private lemma abs_intCast_div16 (n : ℤ) :
    |(n : ℚ) / 10 ^ 16| = ((|n| : ℤ) : ℚ) / 10 ^ 16 := by
  rw [abs_div, abs_of_pos (by positivity : (0:ℚ) < (10:ℚ) ^ 16)]
  push_cast
  ring_nf

set_option maxHeartbeats 1600000 in
-- `push_cast` in the shared closer is a no-op on one of the six branch
-- directions; the linter flags exactly that instance.
set_option linter.unusedTactic false in
/-- Every row-rational weight of `tieredHs_lt` enters through its `num`/`den`
pair (exact, `Rat.num_div_den`; `Rat` denominators are positive), and each
tier comparison is cross-multiplied into an integer polynomial inequality;
vertex coordinates enter as scale-`10¹⁶` integer numerators. Unconditional. -/
private lemma tieredHs_lt_intN_iff
    (e : HScalars) (εθ εφ kT soB fsB kR g p0 p1 p2 : ℚ)
    (na0 da0 na1 da1 na2 da2 nb0 db0 nb1 db1 nb2 db2 nc0 dc0 nc1 dc1 nc2 dc2 nd0 dd0 nd1 dd1 nd2 dd2 ne0 de0 ne1 de1 ne2 de2 nf0 df0 nf1 df1 nf2 df2 gn gdn tn tdn un udn ktn ktdn sn sdn fn fdn kn kdn p0N p1N p2N : ℤ)
    (ha0 : e.a0 = (na0 : ℚ) / (da0 : ℚ)) (hqa0 : (0:ℤ) < da0)
    (ha1 : e.a1 = (na1 : ℚ) / (da1 : ℚ)) (hqa1 : (0:ℤ) < da1)
    (ha2 : e.a2 = (na2 : ℚ) / (da2 : ℚ)) (hqa2 : (0:ℤ) < da2)
    (hb0 : e.b0 = (nb0 : ℚ) / (db0 : ℚ)) (hqb0 : (0:ℤ) < db0)
    (hb1 : e.b1 = (nb1 : ℚ) / (db1 : ℚ)) (hqb1 : (0:ℤ) < db1)
    (hb2 : e.b2 = (nb2 : ℚ) / (db2 : ℚ)) (hqb2 : (0:ℤ) < db2)
    (hc0 : e.c0 = (nc0 : ℚ) / (dc0 : ℚ)) (hqc0 : (0:ℤ) < dc0)
    (hc1 : e.c1 = (nc1 : ℚ) / (dc1 : ℚ)) (hqc1 : (0:ℤ) < dc1)
    (hc2 : e.c2 = (nc2 : ℚ) / (dc2 : ℚ)) (hqc2 : (0:ℤ) < dc2)
    (hd0 : e.d0 = (nd0 : ℚ) / (dd0 : ℚ)) (hqd0 : (0:ℤ) < dd0)
    (hd1 : e.d1 = (nd1 : ℚ) / (dd1 : ℚ)) (hqd1 : (0:ℤ) < dd1)
    (hd2 : e.d2 = (nd2 : ℚ) / (dd2 : ℚ)) (hqd2 : (0:ℤ) < dd2)
    (he0 : e.e0 = (ne0 : ℚ) / (de0 : ℚ)) (hqe0 : (0:ℤ) < de0)
    (he1 : e.e1 = (ne1 : ℚ) / (de1 : ℚ)) (hqe1 : (0:ℤ) < de1)
    (he2 : e.e2 = (ne2 : ℚ) / (de2 : ℚ)) (hqe2 : (0:ℤ) < de2)
    (hf0 : e.f0 = (nf0 : ℚ) / (df0 : ℚ)) (hqf0 : (0:ℤ) < df0)
    (hf1 : e.f1 = (nf1 : ℚ) / (df1 : ℚ)) (hqf1 : (0:ℤ) < df1)
    (hf2 : e.f2 = (nf2 : ℚ) / (df2 : ℚ)) (hqf2 : (0:ℤ) < df2)
    (hgq : g = (gn : ℚ) / (gdn : ℚ)) (hqgq : (0:ℤ) < gdn)
    (htq : εθ = (tn : ℚ) / (tdn : ℚ)) (hqtq : (0:ℤ) < tdn)
    (huq : εφ = (un : ℚ) / (udn : ℚ)) (hquq : (0:ℤ) < udn)
    (hktq : kT = (ktn : ℚ) / (ktdn : ℚ)) (hqktq : (0:ℤ) < ktdn)
    (hsq : soB = (sn : ℚ) / (sdn : ℚ)) (hqsq : (0:ℤ) < sdn)
    (hfq : fsB = (fn : ℚ) / (fdn : ℚ)) (hqfq : (0:ℤ) < fdn)
    (hkq : kR = (kn : ℚ) / (kdn : ℚ)) (hqkq : (0:ℤ) < kdn)
    (hp0 : p0 = (p0N : ℚ) / 10 ^ 16) (hp1 : p1 = (p1N : ℚ) / 10 ^ 16)
    (hp2 : p2 = (p2N : ℚ) / 10 ^ 16) :
    ((decide (gn * ((da0 * (da1 * da2)) * 10 ^ 16 * (fdn * kdn)) >
      (na0 * (da1 * da2) * p0N + na1 * (da0 * da2) * p1N + na2 * (da0 * da1) * p2N) * (gdn * (fdn * kdn))
      + fn * (|p0N| + |p1N| + |p2N|) * (gdn * ((da0 * (da1 * da2)) * kdn))
      + kn * (gdn * ((da0 * (da1 * da2)) * 10 ^ 16 * fdn))) ||
      decide (gn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (10 ^ 16 * (tdn ^ 3 * (udn ^ 3 * (6 * (sdn * ktdn)))))))) >
      (na0 * (da1 * da2) * p0N + na1 * (da0 * da2) * p1N + na2 * (da0 * da1) * p2N) * (gdn * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (tdn ^ 3 * (udn ^ 3 * (6 * (sdn * ktdn)))))))
      + tn * |nb0 * (db1 * db2) * p0N + nb1 * (db0 * db2) * p1N + nb2 * (db0 * db1) * p2N| * (gdn * ((da0 * (da1 * da2)) * ((dc0 * (dc1 * dc2)) * (tdn ^ 2 * (udn ^ 3 * (6 * (sdn * ktdn)))))))
      + un * |nc0 * (dc1 * dc2) * p0N + nc1 * (dc0 * dc2) * p1N + nc2 * (dc0 * dc1) * p2N| * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * (tdn ^ 3 * (udn ^ 2 * (6 * (sdn * ktdn)))))))
      + sn * (|p0N| + |p1N| + |p2N|) * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (tdn ^ 3 * (udn ^ 3 * (6 * ktdn)))))))
      + (tn * udn + un * tdn) ^ 3 * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (10 ^ 16 * (sdn * ktdn))))))
      + ktn * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (10 ^ 16 * (tdn ^ 3 * (udn ^ 3 * (6 * sdn))))))))) ||
      decide (gn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (((dd0 * (dd1 * dd2)) * ((de0 * (de1 * de2)) * (df0 * (df1 * df2)))) * (10 ^ 16 * (tdn ^ 3 * (udn ^ 3 * (6 * ktdn)))))))) >
      (na0 * (da1 * da2) * p0N + na1 * (da0 * da2) * p1N + na2 * (da0 * da1) * p2N) * (gdn * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (((dd0 * (dd1 * dd2)) * ((de0 * (de1 * de2)) * (df0 * (df1 * df2)))) * (tdn ^ 3 * (udn ^ 3 * (6 * ktdn)))))))
      + tn * |nb0 * (db1 * db2) * p0N + nb1 * (db0 * db2) * p1N + nb2 * (db0 * db1) * p2N| * (gdn * ((da0 * (da1 * da2)) * ((dc0 * (dc1 * dc2)) * (((dd0 * (dd1 * dd2)) * ((de0 * (de1 * de2)) * (df0 * (df1 * df2)))) * (tdn ^ 2 * (udn ^ 3 * (6 * ktdn)))))))
      + un * |nc0 * (dc1 * dc2) * p0N + nc1 * (dc0 * dc2) * p1N + nc2 * (dc0 * dc1) * p2N| * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * (((dd0 * (dd1 * dd2)) * ((de0 * (de1 * de2)) * (df0 * (df1 * df2)))) * (tdn ^ 3 * (udn ^ 2 * (6 * ktdn)))))))
      + tn ^ 2 * |nd0 * (dd1 * dd2) * p0N + nd1 * (dd0 * dd2) * p1N + nd2 * (dd0 * dd1) * p2N| * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * ((de0 * (de1 * de2)) * ((df0 * (df1 * df2)) * (tdn * (udn ^ 3 * (3 * ktdn)))))))))
      + tn * un * |ne0 * (de1 * de2) * p0N + ne1 * (de0 * de2) * p1N + ne2 * (de0 * de1) * p2N| * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * ((dd0 * (dd1 * dd2)) * ((df0 * (df1 * df2)) * (tdn ^ 2 * (udn ^ 2 * (6 * ktdn)))))))))
      + un ^ 2 * |nf0 * (df1 * df2) * p0N + nf1 * (df0 * df2) * p1N + nf2 * (df0 * df1) * p2N| * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * ((dd0 * (dd1 * dd2)) * ((de0 * (de1 * de2)) * (tdn ^ 3 * (udn * (3 * ktdn)))))))))
      + (tn * udn + un * tdn) ^ 3 * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (((dd0 * (dd1 * dd2)) * ((de0 * (de1 * de2)) * (df0 * (df1 * df2)))) * (10 ^ 16 * ktdn))))))
      + ktn * (gdn * ((da0 * (da1 * da2)) * ((db0 * (db1 * db2)) * ((dc0 * (dc1 * dc2)) * (((dd0 * (dd1 * dd2)) * ((de0 * (de1 * de2)) * (df0 * (df1 * df2)))) * (10 ^ 16 * (tdn ^ 3 * (udn ^ 3 * 6)))))))))) = true) ↔
    tieredHs_lt e εθ εφ kT soB fsB kR g p0 p1 p2 = true := by
  unfold tieredHs_lt cheapestHs cheapHs fastHs
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  have hqa0Q : (0:ℚ) < (da0 : ℚ) := by exact_mod_cast hqa0
  have hqa0N : ((da0 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqa0Q
  have hqa1Q : (0:ℚ) < (da1 : ℚ) := by exact_mod_cast hqa1
  have hqa1N : ((da1 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqa1Q
  have hqa2Q : (0:ℚ) < (da2 : ℚ) := by exact_mod_cast hqa2
  have hqa2N : ((da2 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqa2Q
  have hqb0Q : (0:ℚ) < (db0 : ℚ) := by exact_mod_cast hqb0
  have hqb0N : ((db0 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqb0Q
  have hqb1Q : (0:ℚ) < (db1 : ℚ) := by exact_mod_cast hqb1
  have hqb1N : ((db1 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqb1Q
  have hqb2Q : (0:ℚ) < (db2 : ℚ) := by exact_mod_cast hqb2
  have hqb2N : ((db2 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqb2Q
  have hqc0Q : (0:ℚ) < (dc0 : ℚ) := by exact_mod_cast hqc0
  have hqc0N : ((dc0 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqc0Q
  have hqc1Q : (0:ℚ) < (dc1 : ℚ) := by exact_mod_cast hqc1
  have hqc1N : ((dc1 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqc1Q
  have hqc2Q : (0:ℚ) < (dc2 : ℚ) := by exact_mod_cast hqc2
  have hqc2N : ((dc2 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqc2Q
  have hqd0Q : (0:ℚ) < (dd0 : ℚ) := by exact_mod_cast hqd0
  have hqd0N : ((dd0 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqd0Q
  have hqd1Q : (0:ℚ) < (dd1 : ℚ) := by exact_mod_cast hqd1
  have hqd1N : ((dd1 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqd1Q
  have hqd2Q : (0:ℚ) < (dd2 : ℚ) := by exact_mod_cast hqd2
  have hqd2N : ((dd2 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqd2Q
  have hqe0Q : (0:ℚ) < (de0 : ℚ) := by exact_mod_cast hqe0
  have hqe0N : ((de0 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqe0Q
  have hqe1Q : (0:ℚ) < (de1 : ℚ) := by exact_mod_cast hqe1
  have hqe1N : ((de1 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqe1Q
  have hqe2Q : (0:ℚ) < (de2 : ℚ) := by exact_mod_cast hqe2
  have hqe2N : ((de2 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqe2Q
  have hqf0Q : (0:ℚ) < (df0 : ℚ) := by exact_mod_cast hqf0
  have hqf0N : ((df0 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqf0Q
  have hqf1Q : (0:ℚ) < (df1 : ℚ) := by exact_mod_cast hqf1
  have hqf1N : ((df1 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqf1Q
  have hqf2Q : (0:ℚ) < (df2 : ℚ) := by exact_mod_cast hqf2
  have hqf2N : ((df2 : ℤ) : ℚ) ≠ 0 := ne_of_gt hqf2Q
  have hqgqQ : (0:ℚ) < (gdn : ℚ) := by exact_mod_cast hqgq
  have hqgqN : ((gdn : ℤ) : ℚ) ≠ 0 := ne_of_gt hqgqQ
  have hqtqQ : (0:ℚ) < (tdn : ℚ) := by exact_mod_cast hqtq
  have hqtqN : ((tdn : ℤ) : ℚ) ≠ 0 := ne_of_gt hqtqQ
  have hquqQ : (0:ℚ) < (udn : ℚ) := by exact_mod_cast hquq
  have hquqN : ((udn : ℤ) : ℚ) ≠ 0 := ne_of_gt hquqQ
  have hqktqQ : (0:ℚ) < (ktdn : ℚ) := by exact_mod_cast hqktq
  have hqktqN : ((ktdn : ℤ) : ℚ) ≠ 0 := ne_of_gt hqktqQ
  have hqsqQ : (0:ℚ) < (sdn : ℚ) := by exact_mod_cast hqsq
  have hqsqN : ((sdn : ℤ) : ℚ) ≠ 0 := ne_of_gt hqsqQ
  have hqfqQ : (0:ℚ) < (fdn : ℚ) := by exact_mod_cast hqfq
  have hqfqN : ((fdn : ℤ) : ℚ) ≠ 0 := ne_of_gt hqfqQ
  have hqkqQ : (0:ℚ) < (kdn : ℚ) := by exact_mod_cast hqkq
  have hqkqN : ((kdn : ℤ) : ℚ) ≠ 0 := ne_of_gt hqkqQ
  rw [ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2, hd0, hd1, hd2, he0, he1, he2, hf0, hf1, hf2, hgq, htq, huq, hktq, hsq, hfq, hkq, hp0, hp1, hp2]
  rw [show (na0 : ℚ) / (da0 : ℚ) * ((p0N : ℚ) / 10 ^ 16) + (na1 : ℚ) / (da1 : ℚ) * ((p1N : ℚ) / 10 ^ 16)
        + (na2 : ℚ) / (da2 : ℚ) * ((p2N : ℚ) / 10 ^ 16)
      = ((na0 * (da1 * da2) * p0N + na1 * (da0 * da2) * p1N + na2 * (da0 * da1) * p2N : ℤ) : ℚ) / ((da0 * (da1 * da2) * 10 ^ 16 : ℤ) : ℚ) from by
    push_cast
    field_simp
    ring]
  rw [show (nb0 : ℚ) / (db0 : ℚ) * ((p0N : ℚ) / 10 ^ 16) + (nb1 : ℚ) / (db1 : ℚ) * ((p1N : ℚ) / 10 ^ 16)
        + (nb2 : ℚ) / (db2 : ℚ) * ((p2N : ℚ) / 10 ^ 16)
      = ((nb0 * (db1 * db2) * p0N + nb1 * (db0 * db2) * p1N + nb2 * (db0 * db1) * p2N : ℤ) : ℚ) / ((db0 * (db1 * db2) * 10 ^ 16 : ℤ) : ℚ) from by
    push_cast
    field_simp
    ring]
  rw [show (nc0 : ℚ) / (dc0 : ℚ) * ((p0N : ℚ) / 10 ^ 16) + (nc1 : ℚ) / (dc1 : ℚ) * ((p1N : ℚ) / 10 ^ 16)
        + (nc2 : ℚ) / (dc2 : ℚ) * ((p2N : ℚ) / 10 ^ 16)
      = ((nc0 * (dc1 * dc2) * p0N + nc1 * (dc0 * dc2) * p1N + nc2 * (dc0 * dc1) * p2N : ℤ) : ℚ) / ((dc0 * (dc1 * dc2) * 10 ^ 16 : ℤ) : ℚ) from by
    push_cast
    field_simp
    ring]
  rw [show (nd0 : ℚ) / (dd0 : ℚ) * ((p0N : ℚ) / 10 ^ 16) + (nd1 : ℚ) / (dd1 : ℚ) * ((p1N : ℚ) / 10 ^ 16)
        + (nd2 : ℚ) / (dd2 : ℚ) * ((p2N : ℚ) / 10 ^ 16)
      = ((nd0 * (dd1 * dd2) * p0N + nd1 * (dd0 * dd2) * p1N + nd2 * (dd0 * dd1) * p2N : ℤ) : ℚ) / ((dd0 * (dd1 * dd2) * 10 ^ 16 : ℤ) : ℚ) from by
    push_cast
    field_simp
    ring]
  rw [show (ne0 : ℚ) / (de0 : ℚ) * ((p0N : ℚ) / 10 ^ 16) + (ne1 : ℚ) / (de1 : ℚ) * ((p1N : ℚ) / 10 ^ 16)
        + (ne2 : ℚ) / (de2 : ℚ) * ((p2N : ℚ) / 10 ^ 16)
      = ((ne0 * (de1 * de2) * p0N + ne1 * (de0 * de2) * p1N + ne2 * (de0 * de1) * p2N : ℤ) : ℚ) / ((de0 * (de1 * de2) * 10 ^ 16 : ℤ) : ℚ) from by
    push_cast
    field_simp
    ring]
  rw [show (nf0 : ℚ) / (df0 : ℚ) * ((p0N : ℚ) / 10 ^ 16) + (nf1 : ℚ) / (df1 : ℚ) * ((p1N : ℚ) / 10 ^ 16)
        + (nf2 : ℚ) / (df2 : ℚ) * ((p2N : ℚ) / 10 ^ 16)
      = ((nf0 * (df1 * df2) * p0N + nf1 * (df0 * df2) * p1N + nf2 * (df0 * df1) * p2N : ℤ) : ℚ) / ((df0 * (df1 * df2) * 10 ^ 16 : ℤ) : ℚ) from by
    push_cast
    field_simp
    ring]
  rw [abs_intCast_div (nb0 * (db1 * db2) * p0N + nb1 * (db0 * db2) * p1N + nb2 * (db0 * db1) * p2N) (db0 * (db1 * db2) * 10 ^ 16) (by positivity)]
  rw [abs_intCast_div (nc0 * (dc1 * dc2) * p0N + nc1 * (dc0 * dc2) * p1N + nc2 * (dc0 * dc1) * p2N) (dc0 * (dc1 * dc2) * 10 ^ 16) (by positivity)]
  rw [abs_intCast_div (nd0 * (dd1 * dd2) * p0N + nd1 * (dd0 * dd2) * p1N + nd2 * (dd0 * dd1) * p2N) (dd0 * (dd1 * dd2) * 10 ^ 16) (by positivity)]
  rw [abs_intCast_div (ne0 * (de1 * de2) * p0N + ne1 * (de0 * de2) * p1N + ne2 * (de0 * de1) * p2N) (de0 * (de1 * de2) * 10 ^ 16) (by positivity)]
  rw [abs_intCast_div (nf0 * (df1 * df2) * p0N + nf1 * (df0 * df2) * p1N + nf2 * (df0 * df1) * p2N) (df0 * (df1 * df2) * 10 ^ 16) (by positivity)]
  rw [abs_intCast_div16 p0N, abs_intCast_div16 p1N, abs_intCast_div16 p2N]
  refine or_congr (or_congr ?_ ?_) ?_ <;>
    · constructor <;> intro h <;> qify at h ⊢ <;> push_cast at h ⊢ <;>
        field_simp at h ⊢ <;> ring_nf at h ⊢ <;> linarith

end Gℚ_gt_maxHℚ


namespace Gℚ_gt_maxHℚ

private lemma ratSplit (q : ℚ) : q = (q.num : ℚ) / ((q.den : ℤ) : ℚ) := by
  push_cast
  exact (Rat.num_div_den q).symm

private lemma ratDenPos (q : ℚ) : (0:ℤ) < ((q.den : ℤ) : ℤ) := by exact_mod_cast q.pos

end Gℚ_gt_maxHℚ

open Gℚ_gt_maxHℚ in
/-- Integer core of `Gℚ_gt_maxHℚ_check`: the same per-pose ℚ work (entries,
`fastG`, the tier scalars), but the per-vertex tier tests are integer
polynomial inequalities — every row-rational weight enters through its
`num`/`den` pair, and the vertex coordinates through the scale-`10¹⁶`
integer table `vN`. Under `decide +kernel` each vertex then costs a handful
of GMP operations instead of dozens of `Rat` reductions. -/
def Gℚ_gt_maxHℚ_checkN {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (S : Fin 3 → ℚ)
    (vN : ι → Fin 3 → ℤ) (w : Fin 2 → ℚ) : Bool :=
  let hs := (hEntriesR p w).scalars
  let g := fastG (gEntriesR p w) εα εθ₁ εφ₁ S
  let kappaTerm := 3 * κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂) ^ 2 / 2)
  let soB := soBound hs εθ₂ εφ₂
  let fsB := foBound hs εθ₂ εφ₂ + soB
  let kR := (εθ₂ + εφ₂) ^ 3 / 6 + kappaTerm
  decide <| ∀ k : ι,
    let p0N := vN k 0
    let p1N := vN k 1
    let p2N := vN k 2
    ((decide (g.num * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * 10 ^ 16 * ((fsB.den : ℤ) * (kR.den : ℤ))) >
          ((hs.a0).num * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ)) * p0N + (hs.a1).num * (((hs.a0).den : ℤ) * ((hs.a2).den : ℤ)) * p1N + (hs.a2).num * (((hs.a0).den : ℤ) * ((hs.a1).den : ℤ)) * p2N) * ((g.den : ℤ) * ((fsB.den : ℤ) * (kR.den : ℤ)))
          + fsB.num * (|p0N| + |p1N| + |p2N|) * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * (kR.den : ℤ)))
          + kR.num * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * 10 ^ 16 * (fsB.den : ℤ)))) ||
      decide (g.num * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (10 ^ 16 * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 3 * (6 * ((soB.den : ℤ) * (kappaTerm.den : ℤ))))))))) >
            ((hs.a0).num * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ)) * p0N + (hs.a1).num * (((hs.a0).den : ℤ) * ((hs.a2).den : ℤ)) * p1N + (hs.a2).num * (((hs.a0).den : ℤ) * ((hs.a1).den : ℤ)) * p2N) * ((g.den : ℤ) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 3 * (6 * ((soB.den : ℤ) * (kappaTerm.den : ℤ))))))))
            + εθ₂.num * |(hs.b0).num * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ)) * p0N + (hs.b1).num * (((hs.b0).den : ℤ) * ((hs.b2).den : ℤ)) * p1N + (hs.b2).num * (((hs.b0).den : ℤ) * ((hs.b1).den : ℤ)) * p2N| * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * ((εθ₂.den : ℤ) ^ 2 * ((εφ₂.den : ℤ) ^ 3 * (6 * ((soB.den : ℤ) * (kappaTerm.den : ℤ))))))))
            + εφ₂.num * |(hs.c0).num * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ)) * p0N + (hs.c1).num * (((hs.c0).den : ℤ) * ((hs.c2).den : ℤ)) * p1N + (hs.c2).num * (((hs.c0).den : ℤ) * ((hs.c1).den : ℤ)) * p2N| * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 2 * (6 * ((soB.den : ℤ) * (kappaTerm.den : ℤ))))))))
            + soB.num * (|p0N| + |p1N| + |p2N|) * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 3 * (6 * (kappaTerm.den : ℤ))))))))
            + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (10 ^ 16 * ((soB.den : ℤ) * (kappaTerm.den : ℤ)))))))
            + kappaTerm.num * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (10 ^ 16 * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 3 * (6 * (soB.den : ℤ)))))))))) ||
      decide (g.num * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * (((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))))) * (10 ^ 16 * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 3 * (6 * (kappaTerm.den : ℤ))))))))) >
            ((hs.a0).num * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ)) * p0N + (hs.a1).num * (((hs.a0).den : ℤ) * ((hs.a2).den : ℤ)) * p1N + (hs.a2).num * (((hs.a0).den : ℤ) * ((hs.a1).den : ℤ)) * p2N) * ((g.den : ℤ) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * (((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))))) * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 3 * (6 * (kappaTerm.den : ℤ))))))))
            + εθ₂.num * |(hs.b0).num * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ)) * p0N + (hs.b1).num * (((hs.b0).den : ℤ) * ((hs.b2).den : ℤ)) * p1N + (hs.b2).num * (((hs.b0).den : ℤ) * ((hs.b1).den : ℤ)) * p2N| * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * (((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))))) * ((εθ₂.den : ℤ) ^ 2 * ((εφ₂.den : ℤ) ^ 3 * (6 * (kappaTerm.den : ℤ))))))))
            + εφ₂.num * |(hs.c0).num * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ)) * p0N + (hs.c1).num * (((hs.c0).den : ℤ) * ((hs.c2).den : ℤ)) * p1N + (hs.c2).num * (((hs.c0).den : ℤ) * ((hs.c1).den : ℤ)) * p2N| * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * (((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * (((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))))) * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 2 * (6 * (kappaTerm.den : ℤ))))))))
            + εθ₂.num ^ 2 * |(hs.d0).num * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ)) * p0N + (hs.d1).num * (((hs.d0).den : ℤ) * ((hs.d2).den : ℤ)) * p1N + (hs.d2).num * (((hs.d0).den : ℤ) * ((hs.d1).den : ℤ)) * p2N| * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * ((((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))) * ((εθ₂.den : ℤ) * ((εφ₂.den : ℤ) ^ 3 * (3 * (kappaTerm.den : ℤ))))))))))
            + εθ₂.num * εφ₂.num * |(hs.e0).num * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ)) * p0N + (hs.e1).num * (((hs.e0).den : ℤ) * ((hs.e2).den : ℤ)) * p1N + (hs.e2).num * (((hs.e0).den : ℤ) * ((hs.e1).den : ℤ)) * p2N| * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * ((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))) * ((εθ₂.den : ℤ) ^ 2 * ((εφ₂.den : ℤ) ^ 2 * (6 * (kappaTerm.den : ℤ))))))))))
            + εφ₂.num ^ 2 * |(hs.f0).num * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ)) * p0N + (hs.f1).num * (((hs.f0).den : ℤ) * ((hs.f2).den : ℤ)) * p1N + (hs.f2).num * (((hs.f0).den : ℤ) * ((hs.f1).den : ℤ)) * p2N| * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * ((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) * (3 * (kappaTerm.den : ℤ))))))))))
            + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * (((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))))) * (10 ^ 16 * (kappaTerm.den : ℤ)))))))
            + kappaTerm.num * ((g.den : ℤ) * ((((hs.a0).den : ℤ) * (((hs.a1).den : ℤ) * ((hs.a2).den : ℤ))) * ((((hs.b0).den : ℤ) * (((hs.b1).den : ℤ) * ((hs.b2).den : ℤ))) * ((((hs.c0).den : ℤ) * (((hs.c1).den : ℤ) * ((hs.c2).den : ℤ))) * (((((hs.d0).den : ℤ) * (((hs.d1).den : ℤ) * ((hs.d2).den : ℤ))) * ((((hs.e0).den : ℤ) * (((hs.e1).den : ℤ) * ((hs.e2).den : ℤ))) * (((hs.f0).den : ℤ) * (((hs.f1).den : ℤ) * ((hs.f2).den : ℤ))))) * (10 ^ 16 * ((εθ₂.den : ℤ) ^ 3 * ((εφ₂.den : ℤ) ^ 3 * 6)))))))))) = true)

open Gℚ_gt_maxHℚ in
/-- The integer core computes exactly the ℚ check (unconditionally). -/
theorem Gℚ_gt_maxHℚ_checkN_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (S : Fin 3 → ℚ)
    (poly : Polyhedron ι (Fin 3 → ℚ)) (vN : ι → Fin 3 → ℤ)
    (hvN : ∀ k (c : Fin 3), poly.v k c = (vN k c : ℚ) / 10 ^ 16) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ_checkN p εα εθ₁ εφ₁ εθ₂ εφ₂ S vN w
      = Gℚ_gt_maxHℚ_check p εα εθ₁ εφ₁ εθ₂ εφ₂ S poly w := by
  rw [Bool.eq_iff_iff]
  unfold Gℚ_gt_maxHℚ_checkN Gℚ_gt_maxHℚ_check
  simp only [decide_eq_true_eq]
  refine forall_congr' fun k => ?_
  exact tieredHs_lt_intN_iff
    (ha0 := ratSplit _) (hqa0 := ratDenPos _)
    (ha1 := ratSplit _) (hqa1 := ratDenPos _)
    (ha2 := ratSplit _) (hqa2 := ratDenPos _)
    (hb0 := ratSplit _) (hqb0 := ratDenPos _)
    (hb1 := ratSplit _) (hqb1 := ratDenPos _)
    (hb2 := ratSplit _) (hqb2 := ratDenPos _)
    (hc0 := ratSplit _) (hqc0 := ratDenPos _)
    (hc1 := ratSplit _) (hqc1 := ratDenPos _)
    (hc2 := ratSplit _) (hqc2 := ratDenPos _)
    (hd0 := ratSplit _) (hqd0 := ratDenPos _)
    (hd1 := ratSplit _) (hqd1 := ratDenPos _)
    (hd2 := ratSplit _) (hqd2 := ratDenPos _)
    (he0 := ratSplit _) (hqe0 := ratDenPos _)
    (he1 := ratSplit _) (hqe1 := ratDenPos _)
    (he2 := ratSplit _) (hqe2 := ratDenPos _)
    (hf0 := ratSplit _) (hqf0 := ratDenPos _)
    (hf1 := ratSplit _) (hqf1 := ratDenPos _)
    (hf2 := ratSplit _) (hqf2 := ratDenPos _)
    (hgq := ratSplit _) (hqgq := ratDenPos _)
    (htq := ratSplit _) (hqtq := ratDenPos _)
    (huq := ratSplit _) (hquq := ratDenPos _)
    (hktq := ratSplit _) (hqktq := ratDenPos _)
    (hsq := ratSplit _) (hqsq := ratDenPos _)
    (hfq := ratSplit _) (hqfq := ratDenPos _)
    (hkq := ratSplit _) (hqkq := ratDenPos _)
    (hp0 := hvN k 0) (hp1 := hvN k 1) (hp2 := hvN k 2)

/-- `Gℚ_gt_maxHℚ_check_iff` through the integer core. -/
theorem Gℚ_gt_maxHℚ_checkN_iff {ι : Type} [Fintype ι] [DecidableEq ι] [ne : Nonempty ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ : ℚ) {εθ₂ εφ₂ : ℚ} (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (S : Fin 3 → ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (vN : ι → Fin 3 → ℤ)
    (hvN : ∀ k (c : Fin 3), poly.v k c = (vN k c : ℚ) / 10 ^ 16) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ_checkN p εα εθ₁ εφ₁ εθ₂ εφ₂ S vN w = true ↔
      Gℚ p εα εθ₁ εφ₁ S w > maxHℚ p poly εθ₂ εφ₂ w := by
  rw [Gℚ_gt_maxHℚ_checkN_eq p εα εθ₁ εφ₁ εθ₂ εφ₂ S poly vN hvN w]
  exact Gℚ_gt_maxHℚ_check_iff p εα εθ₁ εφ₁ hεθ₂ hεφ₂ S poly w

/-! ## All-Nat fast path for the kernel-only route

`Gℚ_gt_maxHℚ_fastNat` decides the same tiered test as `Gℚ_gt_maxHℚ_checkN`,
but one-sidedly (`true` implies the ℚ check; `false` means "fall back")
and with every per-vertex operation a single kernel-accelerated `Nat`
primitive:

* vertex coordinates come from a packed table literal (57-bit binary
  fields, offset-encoded `coord·10¹⁶ + 2⁵⁶`, 171 bits per vertex — see
  `Vertices/PythonNat.lean`), one shift + mask per vertex;
* the per-pose scalars are computed once, exactly, in fixed-scale `ℤ`
  (numerator `ediv` mirroring `round13`), then conservatively rounded to
  fixed power-of-10 scales — `g` down (`glo ≤ g·10¹³`), all the bound
  scalars up — so each tier comparison cross-multiplies into a pure-`Nat`
  inequality with *fixed* denominators instead of per-row `Rat.den`
  products;
* signed per-vertex dot products use offset algebra: with `â = a + 2⁴⁷`,
  `p̂ = p + 2⁵⁶` all `Nat`, `a·p = (Σâp̂ + 3·2¹⁰³) − (2⁵⁶Σâ + 2⁴⁷Σp̂)`, and
  the absolute values the tiers need are one comparison + subtraction;
* the loop is structural `Nat` recursion (no `Fintype`/`Finset.univ`
  walk).

Row-level guards (`0 < wd`, `0 ≤ ε` numerators, `0 < glo`, offset
nonnegativity) make the soundness direction unconditional; rows that fail
any guard or any tier return `false` and are re-decided by the exact
checker. -/

namespace Gℚ_gt_maxHℚ

/-- `|x − y|` on `ℕ` (one comparison + one subtraction). -/
@[inline] def natAbsDiff (x y : ℕ) : ℕ := if x ≤ y then y - x else x - y

/-- Ceiling division `⌈n/d⌉` (for `0 < d`). -/
@[inline] def cdiv (n d : ℤ) : ℤ := -(-n / d)

/-- Offset-nonnegativity guard for a scale-13 entry. -/
@[inline] def offOk (x : ℤ) : Bool := decide (0 ≤ x + 2 ^ 47)

/-- The per-vertex tier test on extracted (offset) vertex fields
`P0 P1 P2`. The tier-1 path — which decides all but the near-binding
vertices — is written directly in the kernel's accelerated `Nat` primitives
(`Nat.mul`/`Nat.add`/`Nat.ble`/`Nat.blt`/`Nat.sub`/`cond`), bypassing the
`HMul`/`Decidable` instance wrappers, which measurably halve kernel
throughput; the rare tier-2/3 fallbacks stay in ordinary notation. -/
private def natTierBody (A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
    D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
    g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 P0 P1 P2 : ℕ) : Bool :=
  let sp := Nat.add (Nat.add P0 P1) P2
  let gsp := Nat.mul (2 ^ 47) sp
  let s := Nat.add (Nat.add
      (cond (Nat.ble P0 (2 ^ 56)) (Nat.sub (2 ^ 56) P0) (Nat.sub P0 (2 ^ 56)))
      (cond (Nat.ble P1 (2 ^ 56)) (Nat.sub (2 ^ 56) P1) (Nat.sub P1 (2 ^ 56))))
      (cond (Nat.ble P2 (2 ^ 56)) (Nat.sub (2 ^ 56) P2) (Nat.sub P2 (2 ^ 56)))
  let XA := Nat.add (Nat.add (Nat.add (Nat.mul A0 P0) (Nat.mul A1 P1))
      (Nat.mul A2 P2)) (3 * 2 ^ 103)
  let CA := Nat.add fsA gsp
  (Nat.blt (Nat.add (Nat.add XA (Nat.mul fsBh s)) kR16) (Nat.add g16 CA)).or
    ((let bp := natAbsDiff (B0 * P0 + B1 * P1 + B2 * P2 + 3 * 2 ^ 103) (fsB + gsp)
      let cp := natAbsDiff (C0 * P0 + C1 * P1 + C2 * P2 + 3 * 2 ^ 103) (fsC + gsp)
      decide (XA * 10 ^ 13 + eθ * bp + eφ * cp + soB13 * s + kR29 < g29 + CA * 10 ^ 13)).or
      (let bp := natAbsDiff (B0 * P0 + B1 * P1 + B2 * P2 + 3 * 2 ^ 103) (fsB + gsp)
       let cp := natAbsDiff (C0 * P0 + C1 * P1 + C2 * P2 + 3 * 2 ^ 103) (fsC + gsp)
       let dp := natAbsDiff (D0 * P0 + D1 * P1 + D2 * P2 + 3 * 2 ^ 103) (fsD + gsp)
       let ep := natAbsDiff (E0 * P0 + E1 * P1 + E2 * P2 + 3 * 2 ^ 103) (fsE + gsp)
       let fp := natAbsDiff (F0 * P0 + F1 * P1 + F2 * P2 + 3 * 2 ^ 103) (fsF + gsp)
       decide (XA * (2 * 10 ^ 26) + (eθ * bp + eφ * cp) * (2 * 10 ^ 13)
           + q1 * dp + q2 * ep + q3 * fp + kR42 < g42 + CA * (2 * 10 ^ 26))))

/-- The all-`Nat` per-vertex loop: extract the three 57-bit offset fields of
flat vertex `j` from the packed table (one accelerated shift + mask each)
and run `natTierBody`; `j` counts down over flat vertex indices. -/
private def natTierLoop (bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
    D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
    g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 : ℕ) : ℕ → Bool
  | 0 => true
  | j + 1 =>
    (let v := Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)
     natTierBody A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
       D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
       g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3
       (Nat.land v (2 ^ 57 - 1)) (Nat.land (Nat.shiftRight v 57) (2 ^ 57 - 1))
       (Nat.shiftRight v 114)).and
    (natTierLoop bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
      D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
      g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 j)

/-! ### Soundness bridges for the fast path -/

/-- `natAbsDiff` casts to an integer absolute difference. -/
private lemma natAbsDiff_cast (x y : ℕ) : ((natAbsDiff x y : ℕ) : ℤ) = |(x : ℤ) - y| := by
  unfold natAbsDiff
  split
  · rename_i h
    rw [abs_sub_comm, abs_of_nonneg (by omega : (0:ℤ) ≤ (y:ℤ) - x)]
    omega
  · rename_i h
    rw [abs_of_nonneg (by omega : (0:ℤ) ≤ (x:ℤ) - y)]
    omega

/-- The raw `cond`/`ble`/`sub` form of `natAbsDiff` used on the tier-1 path. -/
private lemma cond_ble_sub_cast (x c : ℕ) :
    ((cond (Nat.ble x c) (c - x) (x - c) : ℕ) : ℤ) = |(x : ℤ) - c| := by
  rcases hb : Nat.ble x c with _ | _
  · have h : ¬ x ≤ c := fun hle => by
      rw [Nat.ble_eq_true_of_le hle] at hb
      exact Bool.noConfusion hb
    rw [cond_false, abs_of_nonneg (by omega : (0:ℤ) ≤ (x:ℤ) - c)]
    omega
  · have h : x ≤ c := Nat.ble_eq ▸ hb
    rw [cond_true, abs_sub_comm, abs_of_nonneg (by omega : (0:ℤ) ≤ (c:ℤ) - x)]
    omega

/-- `cdiv` bounds the exact quotient from above. -/
private lemma le_cdiv {n d : ℤ} (hd : (0:ℤ) < d) : (n : ℚ) / (d : ℚ) ≤ ((cdiv n d : ℤ) : ℚ) := by
  unfold cdiv
  have hdq : (0:ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [div_le_iff₀ hdq]
  have h1 : n ≤ -(-n / d) * d := by
    have h2 := Int.mul_ediv_add_emod (-n) d
    have h3 := Int.emod_nonneg (-n) (ne_of_gt hd)
    linarith
  exact_mod_cast h1

/-- Integer division bounds the exact quotient from below. -/
private lemma ediv_le {n d : ℤ} (hd : (0:ℤ) < d) : ((n / d : ℤ) : ℚ) ≤ (n : ℚ) / (d : ℚ) := by
  have hdq : (0:ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [le_div_iff₀ hdq]
  have h1 : n / d * d ≤ n := by
    have h2 := Int.mul_ediv_add_emod n d
    have h3 := Int.emod_nonneg n (ne_of_gt hd)
    linarith
  exact_mod_cast h1

/-- Cast an offset-encoded `natAbsDiff` dot product to the absolute value of
the underlying signed dot product (the offsets cancel). -/
private lemma natAbsDiff_offset_cast (x0 x1 x2 y0 y1 y2 : ℤ) (X0 X1 X2 Y0 Y1 Y2 : ℕ)
    (hX0 : (X0 : ℤ) = x0 + 2 ^ 47) (hX1 : (X1 : ℤ) = x1 + 2 ^ 47)
    (hX2 : (X2 : ℤ) = x2 + 2 ^ 47)
    (hY0 : (Y0 : ℤ) = y0 + 2 ^ 56) (hY1 : (Y1 : ℤ) = y1 + 2 ^ 56)
    (hY2 : (Y2 : ℤ) = y2 + 2 ^ 56) :
    ((natAbsDiff (X0 * Y0 + X1 * Y1 + X2 * Y2 + 3 * 2 ^ 103)
        (2 ^ 56 * (X0 + X1 + X2) + 2 ^ 47 * (Y0 + Y1 + Y2)) : ℕ) : ℤ)
      = |x0 * y0 + x1 * y1 + x2 * y2| := by
  rw [natAbsDiff_cast]
  congr 1
  push_cast
  rw [hX0, hX1, hX2, hY0, hY1, hY2]
  ring

/-- Sibling of `abs_intCast_div16` at the dot-product scale. -/
private lemma abs_intCast_div29 (n : ℤ) :
    |(n : ℚ) / 10 ^ 29| = ((|n| : ℤ) : ℚ) / 10 ^ 29 := by
  rw [abs_div, abs_of_pos (by positivity : (0:ℚ) < (10:ℚ) ^ 29)]
  push_cast
  ring_nf

set_option maxHeartbeats 1600000 in
/-- The crux of the fast path: a true `natTierBody` at one vertex implies the
ℚ tiered test at that vertex. Every argument enters through an equation or a
directional bound, so the caller controls the exact pipeline shapes. -/
private lemma natTierBody_sound
    {e : HScalars} {εθ εφ kt soB fsB kR g p0q p1q p2q : ℚ}
    {a0N a1N a2N b0N b1N b2N c0N c1N c2N d0N d1N d2N e0N e1N e2N f0N f1N f2N : ℤ}
    (ha0 : e.a0 = (a0N : ℚ) / 10 ^ 13) (ha1 : e.a1 = (a1N : ℚ) / 10 ^ 13)
    (ha2 : e.a2 = (a2N : ℚ) / 10 ^ 13)
    (hb0 : e.b0 = (b0N : ℚ) / 10 ^ 13) (hb1 : e.b1 = (b1N : ℚ) / 10 ^ 13)
    (hb2 : e.b2 = (b2N : ℚ) / 10 ^ 13)
    (hc0 : e.c0 = (c0N : ℚ) / 10 ^ 13) (hc1 : e.c1 = (c1N : ℚ) / 10 ^ 13)
    (hc2 : e.c2 = (c2N : ℚ) / 10 ^ 13)
    (hd0 : e.d0 = (d0N : ℚ) / 10 ^ 13) (hd1 : e.d1 = (d1N : ℚ) / 10 ^ 13)
    (hd2 : e.d2 = (d2N : ℚ) / 10 ^ 13)
    (he0 : e.e0 = (e0N : ℚ) / 10 ^ 13) (he1 : e.e1 = (e1N : ℚ) / 10 ^ 13)
    (he2 : e.e2 = (e2N : ℚ) / 10 ^ 13)
    (hf0 : e.f0 = (f0N : ℚ) / 10 ^ 13) (hf1 : e.f1 = (f1N : ℚ) / 10 ^ 13)
    (hf2 : e.f2 = (f2N : ℚ) / 10 ^ 13)
    {P0 P1 P2 : ℕ} {p0N p1N p2N : ℤ}
    (hP0 : (P0 : ℤ) = p0N + 2 ^ 56) (hP1 : (P1 : ℤ) = p1N + 2 ^ 56)
    (hP2 : (P2 : ℤ) = p2N + 2 ^ 56)
    (hp0 : p0q = (p0N : ℚ) / 10 ^ 16) (hp1 : p1q = (p1N : ℚ) / 10 ^ 16)
    (hp2 : p2q = (p2N : ℚ) / 10 ^ 16)
    {A0 A1 A2 B0 B1 B2 C0 C1 C2 D0 D1 D2 E0 E1 E2 F0 F1 F2 : ℕ}
    (hA0 : (A0 : ℤ) = a0N + 2 ^ 47) (hA1 : (A1 : ℤ) = a1N + 2 ^ 47)
    (hA2 : (A2 : ℤ) = a2N + 2 ^ 47)
    (hB0 : (B0 : ℤ) = b0N + 2 ^ 47) (hB1 : (B1 : ℤ) = b1N + 2 ^ 47)
    (hB2 : (B2 : ℤ) = b2N + 2 ^ 47)
    (hC0 : (C0 : ℤ) = c0N + 2 ^ 47) (hC1 : (C1 : ℤ) = c1N + 2 ^ 47)
    (hC2 : (C2 : ℤ) = c2N + 2 ^ 47)
    (hD0 : (D0 : ℤ) = d0N + 2 ^ 47) (hD1 : (D1 : ℤ) = d1N + 2 ^ 47)
    (hD2 : (D2 : ℤ) = d2N + 2 ^ 47)
    (hE0 : (E0 : ℤ) = e0N + 2 ^ 47) (hE1 : (E1 : ℤ) = e1N + 2 ^ 47)
    (hE2 : (E2 : ℤ) = e2N + 2 ^ 47)
    (hF0 : (F0 : ℤ) = f0N + 2 ^ 47) (hF1 : (F1 : ℤ) = f1N + 2 ^ 47)
    (hF2 : (F2 : ℤ) = f2N + 2 ^ 47)
    {glo kRhi fsHi soHi eθhi eφhi : ℤ}
    (hglo : ((glo : ℤ) : ℚ) / 10 ^ 13 ≤ g)
    (hkRq : kR = (εθ + εφ) ^ 3 / 6 + kt)
    (hkR : ((εθ + εφ) ^ 3 / 6 + kt) * 10 ^ 13 ≤ ((kRhi : ℤ) : ℚ))
    (hfs : fsB * 10 ^ 13 ≤ ((fsHi : ℤ) : ℚ))
    (hsoB : soB * 10 ^ 13 ≤ ((soHi : ℤ) : ℚ))
    (heθq : εθ * 10 ^ 13 ≤ ((eθhi : ℤ) : ℚ))
    (heφq : εφ * 10 ^ 13 ≤ ((eφhi : ℤ) : ℚ))
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    {fsA fsB' fsC fsD fsE fsF g16 g29 g42 fsBh soB13 kR16 kR29 kR42
     eθN eφN q1 q2 q3 : ℕ}
    (hfsA : fsA = 2 ^ 56 * (A0 + A1 + A2)) (hfsB : fsB' = 2 ^ 56 * (B0 + B1 + B2))
    (hfsC : fsC = 2 ^ 56 * (C0 + C1 + C2)) (hfsD : fsD = 2 ^ 56 * (D0 + D1 + D2))
    (hfsE : fsE = 2 ^ 56 * (E0 + E1 + E2)) (hfsF : fsF = 2 ^ 56 * (F0 + F1 + F2))
    (hg16 : (g16 : ℤ) = glo * 10 ^ 16) (hg29 : (g29 : ℤ) = glo * 10 ^ 29)
    (hg42 : (g42 : ℤ) = 2 * glo * 10 ^ 42)
    (hfsBh : (fsBh : ℤ) = fsHi) (hsoB13 : (soB13 : ℤ) = soHi * 10 ^ 13)
    (hkR16 : (kR16 : ℤ) = kRhi * 10 ^ 16) (hkR29 : (kR29 : ℤ) = kRhi * 10 ^ 29)
    (hkR42 : (kR42 : ℤ) = 2 * kRhi * 10 ^ 42)
    (heθN : (eθN : ℤ) = eθhi) (heφN : (eφN : ℤ) = eφhi)
    (hq1 : (q1 : ℤ) = eθhi ^ 2) (hq2 : (q2 : ℤ) = 2 * eθhi * eφhi)
    (hq3 : (q3 : ℤ) = eφhi ^ 2)
    (h : natTierBody A0 A1 A2 fsA B0 B1 B2 fsB' C0 C1 C2 fsC
      D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
      g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθN eφN q1 q2 q3 P0 P1 P2 = true) :
    tieredHs_lt e εθ εφ kt soB fsB kR g p0q p1q p2q = true := by
  subst hfsA hfsB hfsC hfsD hfsE hfsF
  unfold natTierBody at h
  simp only [Bool.or_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
  unfold tieredHs_lt
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  -- shared ℚ-side facts
  have hSnn : (0:ℚ) ≤ |(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)| := by positivity
  rcases h with h | h | h
  · -- tier 1 ⟹ the `cheapestHs` disjunct
    left; left
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
    zify at h
    rw [cond_ble_sub_cast, cond_ble_sub_cast, cond_ble_sub_cast,
      hg16, hkR16, hfsBh, hP0, hP1, hP2, hA0, hA1, hA2] at h
    push_cast at h
    simp only [add_sub_cancel_right] at h
    have key : a0N * p0N + a1N * p1N + a2N * p2N
        + fsHi * (|p0N| + |p1N| + |p2N|) + kRhi * 10 ^ 16 < glo * 10 ^ 16 := by
      linarith
    have keyQ : ((a0N * p0N + a1N * p1N + a2N * p2N
        + fsHi * (|p0N| + |p1N| + |p2N|) + kRhi * 10 ^ 16 : ℤ) : ℚ)
        < ((glo * 10 ^ 16 : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at keyQ
    have hb1 : fsB * 10 ^ 13 * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|)
        ≤ (fsHi : ℚ) * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|) :=
      mul_le_mul_of_nonneg_right hfs hSnn
    have hkR' : kR * 10 ^ 13 ≤ (kRhi : ℚ) := hkRq ▸ hkR
    unfold cheapestHs
    rw [ha0, ha1, ha2, hp0, hp1, hp2, abs_intCast_div16, abs_intCast_div16,
      abs_intCast_div16]
    push_cast
    linarith
  · -- tier 2 ⟹ the `cheapHs` disjunct
    left; right
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
    zify at h
    rw [cond_ble_sub_cast, cond_ble_sub_cast, cond_ble_sub_cast,
      natAbsDiff_offset_cast b0N b1N b2N p0N p1N p2N B0 B1 B2 P0 P1 P2
        hB0 hB1 hB2 hP0 hP1 hP2,
      natAbsDiff_offset_cast c0N c1N c2N p0N p1N p2N C0 C1 C2 P0 P1 P2
        hC0 hC1 hC2 hP0 hP1 hP2,
      hg29, hkR29, hsoB13, heθN, heφN, hP0, hP1, hP2, hA0, hA1, hA2] at h
    push_cast at h
    simp only [add_sub_cancel_right] at h
    have key : (a0N * p0N + a1N * p1N + a2N * p2N) * 10 ^ 13
        + eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
        + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|
        + soHi * 10 ^ 13 * (|p0N| + |p1N| + |p2N|)
        + kRhi * 10 ^ 29 < glo * 10 ^ 29 := by linarith
    have keyQ : (((a0N * p0N + a1N * p1N + a2N * p2N) * 10 ^ 13
        + eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
        + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|
        + soHi * 10 ^ 13 * (|p0N| + |p1N| + |p2N|)
        + kRhi * 10 ^ 29 : ℤ) : ℚ) < ((glo * 10 ^ 29 : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at keyQ
    have hbq : e.b0 * p0q + e.b1 * p1q + e.b2 * p2q
        = ((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ) / 10 ^ 29 := by
      rw [hb0, hb1, hb2, hp0, hp1, hp2]
      push_cast
      ring
    have hcq : e.c0 * p0q + e.c1 * p1q + e.c2 * p2q
        = ((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ) / 10 ^ 29 := by
      rw [hc0, hc1, hc2, hp0, hp1, hp2]
      push_cast
      ring
    have hbabs : |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        = |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [hbq, abs_intCast_div29]
      push_cast
      ring
    have hcabs : |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        = |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [hcq, abs_intCast_div29]
      push_cast
      ring
    have hbB : εθ * 10 ^ 13 * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heθq (abs_nonneg _)
    have hcB : εφ * 10 ^ 13 * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)|
        ≤ (eφhi : ℚ) * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heφq (abs_nonneg _)
    have hsB : soB * 10 ^ 13 * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|)
        ≤ (soHi : ℚ) * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|) :=
      mul_le_mul_of_nonneg_right hsoB hSnn
    push_cast at hbB hcB hsB
    unfold cheapHs
    rw [ha0, ha1, ha2]
    rw [show (a0N : ℚ) / 10 ^ 13 * p0q + (a1N : ℚ) / 10 ^ 13 * p1q
        + (a2N : ℚ) / 10 ^ 13 * p2q
        + εθ * |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        + εφ * |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        + soB * (|p0q| + |p1q| + |p2q|) + (εθ + εφ) ^ 3 / 6 + kt
        = (a0N : ℚ) / 10 ^ 13 * p0q + (a1N : ℚ) / 10 ^ 13 * p1q
        + (a2N : ℚ) / 10 ^ 13 * p2q
        + εθ * |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        + εφ * |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        + soB * (|p0q| + |p1q| + |p2q|) + ((εθ + εφ) ^ 3 / 6 + kt) from by ring]
    rw [hbabs, hcabs, hp0, hp1, hp2, abs_intCast_div16, abs_intCast_div16,
      abs_intCast_div16]
    push_cast
    linarith
  · -- tier 3 ⟹ the exact `fastHs` disjunct
    right
    simp only [Nat.add_eq, Nat.mul_eq] at h
    zify at h
    rw [natAbsDiff_offset_cast b0N b1N b2N p0N p1N p2N B0 B1 B2 P0 P1 P2
        hB0 hB1 hB2 hP0 hP1 hP2,
      natAbsDiff_offset_cast c0N c1N c2N p0N p1N p2N C0 C1 C2 P0 P1 P2
        hC0 hC1 hC2 hP0 hP1 hP2,
      natAbsDiff_offset_cast d0N d1N d2N p0N p1N p2N D0 D1 D2 P0 P1 P2
        hD0 hD1 hD2 hP0 hP1 hP2,
      natAbsDiff_offset_cast e0N e1N e2N p0N p1N p2N E0 E1 E2 P0 P1 P2
        hE0 hE1 hE2 hP0 hP1 hP2,
      natAbsDiff_offset_cast f0N f1N f2N p0N p1N p2N F0 F1 F2 P0 P1 P2
        hF0 hF1 hF2 hP0 hP1 hP2,
      hg42, hkR42, hq1, hq2, hq3, heθN, heφN, hP0, hP1, hP2, hA0, hA1, hA2] at h
    push_cast at h
    have key : (a0N * p0N + a1N * p1N + a2N * p2N) * (2 * 10 ^ 26)
        + (eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
           + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|) * (2 * 10 ^ 13)
        + eθhi ^ 2 * |d0N * p0N + d1N * p1N + d2N * p2N|
        + 2 * eθhi * eφhi * |e0N * p0N + e1N * p1N + e2N * p2N|
        + eφhi ^ 2 * |f0N * p0N + f1N * p1N + f2N * p2N|
        + 2 * kRhi * 10 ^ 42 < 2 * glo * 10 ^ 42 := by linarith
    have keyQ : (((a0N * p0N + a1N * p1N + a2N * p2N) * (2 * 10 ^ 26)
        + (eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
           + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|) * (2 * 10 ^ 13)
        + eθhi ^ 2 * |d0N * p0N + d1N * p1N + d2N * p2N|
        + 2 * eθhi * eφhi * |e0N * p0N + e1N * p1N + e2N * p2N|
        + eφhi ^ 2 * |f0N * p0N + f1N * p1N + f2N * p2N|
        + 2 * kRhi * 10 ^ 42 : ℤ) : ℚ) < ((2 * glo * 10 ^ 42 : ℤ) : ℚ) := by
      exact_mod_cast key
    push_cast at keyQ
    have hbabs : |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        = |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.b0 * p0q + e.b1 * p1q + e.b2 * p2q
          = ((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hb0, hb1, hb2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hcabs : |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        = |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.c0 * p0q + e.c1 * p1q + e.c2 * p2q
          = ((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hc0, hc1, hc2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hdabs : |e.d0 * p0q + e.d1 * p1q + e.d2 * p2q|
        = |((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.d0 * p0q + e.d1 * p1q + e.d2 * p2q
          = ((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hd0, hd1, hd2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have heabs : |e.e0 * p0q + e.e1 * p1q + e.e2 * p2q|
        = |((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.e0 * p0q + e.e1 * p1q + e.e2 * p2q
          = ((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [he0, he1, he2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hfabs : |e.f0 * p0q + e.f1 * p1q + e.f2 * p2q|
        = |((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.f0 * p0q + e.f1 * p1q + e.f2 * p2q
          = ((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hf0, hf1, hf2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hbB : εθ * 10 ^ 13 * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heθq (abs_nonneg _)
    have hcB : εφ * 10 ^ 13 * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)|
        ≤ (eφhi : ℚ) * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heφq (abs_nonneg _)
    have heθ13 : (0:ℚ) ≤ εθ * 10 ^ 13 := by positivity
    have heφ13 : (0:ℚ) ≤ εφ * 10 ^ 13 := by positivity
    have heθhi0 : (0:ℚ) ≤ (eθhi : ℚ) := le_trans heθ13 heθq
    have heφhi0 : (0:ℚ) ≤ (eφhi : ℚ) := le_trans heφ13 heφq
    have hdB : (εθ * 10 ^ 13) ^ 2 * |((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) ^ 2 * |((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ heθ13 heθq 2) (abs_nonneg _)
    have heB : (εθ * 10 ^ 13) * (εφ * 10 ^ 13)
          * |((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) * (eφhi : ℚ) * |((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul heθq heφq heφ13 heθhi0) (abs_nonneg _)
    have hfB : (εφ * 10 ^ 13) ^ 2 * |((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ)|
        ≤ (eφhi : ℚ) ^ 2 * |((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ heφ13 heφq 2) (abs_nonneg _)
    push_cast at hbB hcB hdB heB hfB
    unfold fastHs
    rw [ha0, ha1, ha2, hbabs, hcabs, hdabs, heabs, hfabs, hp0, hp1, hp2]
    push_cast
    linarith

/-- `round13` of an integer fraction over `10²⁶·wd` (H-entry scale). -/
private lemma round13_intCast_div26 (A : ℤ) (wd : ℕ) :
    RationalApprox.round13 ((A : ℚ) / (10 ^ 26 * (wd : ℚ)))
      = ((A / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have harg : (A : ℚ) / (10 ^ 26 * (wd : ℚ)) * 10 ^ 13
      = (A : ℚ) / ((10 ^ 13 * wd : ℕ) : ℚ) := by
    push_cast
    rw [show (10:ℚ) ^ 26 * (wd : ℚ) = 10 ^ 13 * (10 ^ 13 * (wd : ℚ)) from by ring,
      div_mul_eq_mul_div, mul_comm (A : ℚ) ((10:ℚ) ^ 13),
      mul_div_mul_left _ _ (by norm_num : ((10:ℚ) ^ 13) ≠ 0)]
    norm_num
  have hfl : ⌊(A : ℚ) / (10 ^ 26 * (wd : ℚ)) * 10 ^ 13⌋ = A / (10 ^ 13 * (wd : ℤ)) := by
    rw [harg, Rat.floor_intCast_div_natCast]
    congr 1
  unfold RationalApprox.round13
  rw [hfl]

/-- `round13` of an integer fraction over `10³⁹·wd` (G-entry scale). -/
private lemma round13_intCast_div39 (A : ℤ) (wd : ℕ) :
    RationalApprox.round13 ((A : ℚ) / (10 ^ 39 * (wd : ℚ)))
      = ((A / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have harg : (A : ℚ) / (10 ^ 39 * (wd : ℚ)) * 10 ^ 13
      = (A : ℚ) / ((10 ^ 26 * wd : ℕ) : ℚ) := by
    push_cast
    rw [show (10:ℚ) ^ 39 * (wd : ℚ) = 10 ^ 13 * (10 ^ 26 * (wd : ℚ)) from by ring,
      div_mul_eq_mul_div, mul_comm (A : ℚ) ((10:ℚ) ^ 13),
      mul_div_mul_left _ _ (by norm_num : ((10:ℚ) ^ 13) ≠ 0)]
    norm_num
  have hfl : ⌊(A : ℚ) / (10 ^ 39 * (wd : ℚ)) * 10 ^ 13⌋ = A / (10 ^ 26 * (wd : ℤ)) := by
    rw [harg, Rat.floor_intCast_div_natCast]
    congr 1
  unfold RationalApprox.round13
  rw [hfl]

/-- `cdiv` of a nonnegative numerator is nonnegative. -/
private lemma cdiv_nonneg {n d : ℤ} (hn : 0 ≤ n) (hd : (0:ℤ) < d) : 0 ≤ cdiv n d := by
  have h := le_cdiv (n := n) (d := d) hd
  have hq : (0:ℚ) ≤ (n : ℚ) / (d : ℚ) := by positivity
  exact_mod_cast le_trans hq h
section HEntryBridge

open RationalApprox (sinNum13 cosNum13)

variable {p : Pose ℚ} {w : Fin 2 → ℚ} {wxn wyn : ℤ} {wd : ℕ}

private lemma hentry_a0 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.a0
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2tw 0
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2tw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_a1 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.a1
      = (((cosNum13 p.θ₂ * wxn * 10 ^ 13 - sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2tw 1
      = (((cosNum13 p.θ₂ * wxn * 10 ^ 13 - sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2tw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_a2 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.a2
      = (((sinNum13 p.φ₂ * wyn * 10 ^ 13) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2tw 2
      = (((sinNum13 p.φ₂ * wyn * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2tw 2) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_b0 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.b0
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θtw 0
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_b1 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.b1
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θtw 1
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_c0 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.c0
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φtw 0
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_c1 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.c1
      = (((sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φtw 1
      = (((sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_c2 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.c2
      = (((cosNum13 p.φ₂ * wyn * 10 ^ 13) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φtw 2
      = (((cosNum13 p.φ₂ * wyn * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2φtw 2) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_d0 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.d0
      = (((-(-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn)) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θθtw 0
      = (((-(-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn)) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θθtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_d1 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.d1
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θθtw 1
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θθtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_e0 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.e0
      = (((-(sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn)) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θφtw 0
      = (((-(sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn)) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2θφtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_e1 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.e1
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θφtw 1
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2θφtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_f0 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.f0
      = (((cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φφtw 0
      = (((cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φφtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_f1 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.f1
      = (((sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φφtw 1
      = (((sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φφtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_f2 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.f2
      = (((-(sinNum13 p.φ₂ * wyn * 10 ^ 13)) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φφtw 2
      = (((-(sinNum13 p.φ₂ * wyn * 10 ^ 13)) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2φφtw 2) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

/-- The identically-zero third components round to `0`. -/
private lemma hentry_zero2 (v : Fin 3 → ℚ) (hv : v 2 = 0) :
    RationalApprox.round13 (v 2) = ((0 : ℤ) : ℚ) / 10 ^ 13 := by
  rw [hv]
  unfold RationalApprox.round13
  norm_num

end HEntryBridge

section GDotBridge

open RationalApprox (sinNum13 cosNum13)

variable {p : Pose ℚ} {w : Fin 2 → ℚ} {wxn wyn : ℤ} {wd : ℕ}
  {S : Fin 3 → ℚ} {s0 s1 s2 : ℤ}

private lemma gdot_R (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1RTw ⬝ᵥ S
      = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1RTw 0
      = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1RTw 0) = _
    rw [show (gEntries p w).m1RTw 0 = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1RTw 1
      = (((cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1RTw 1) = _
    rw [show (gEntries p w).m1RTw 1 = (((cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1RTw 2
      = (((sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1RTw 2) = _
    rw [show (gEntries p w).m1RTw 2 = (((sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_R' (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1R'Tw ⬝ᵥ S
      = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1R'Tw 0
      = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1R'Tw 0) = _
    rw [show (gEntries p w).m1R'Tw 0 = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1R'Tw 1
      = (((cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1R'Tw 1) = _
    rw [show (gEntries p w).m1R'Tw 1 = (((cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1R'Tw 2
      = (((-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1R'Tw 2) = _
    rw [show (gEntries p w).m1R'Tw 2 = (((-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_thR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θRTw ⬝ᵥ S
      = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θRTw 0
      = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θRTw 0) = _
    rw [show (gEntries p w).m1θRTw 0 = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θRTw 1
      = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θRTw 1) = _
    rw [show (gEntries p w).m1θRTw 1 = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θRTw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θRTw 2) = _
    rw [show (gEntries p w).m1θRTw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_phR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1φRTw ⬝ᵥ S
      = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1φRTw 0
      = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φRTw 0) = _
    rw [show (gEntries p w).m1φRTw 0 = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1φRTw 1
      = (((sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φRTw 1) = _
    rw [show (gEntries p w).m1φRTw 1 = (((sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1φRTw 2
      = (((cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φRTw 2) = _
    rw [show (gEntries p w).m1φRTw 2 = (((cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_thR' (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θR'Tw ⬝ᵥ S
      = (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θR'Tw 0
      = (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θR'Tw 0) = _
    rw [show (gEntries p w).m1θR'Tw 0 = (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θR'Tw 1
      = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θR'Tw 1) = _
    rw [show (gEntries p w).m1θR'Tw 1 = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θR'Tw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θR'Tw 2) = _
    rw [show (gEntries p w).m1θR'Tw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_phR' (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1φR'Tw ⬝ᵥ S
      = (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1φR'Tw 0
      = (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φR'Tw 0) = _
    rw [show (gEntries p w).m1φR'Tw 0 = (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1φR'Tw 1
      = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φR'Tw 1) = _
    rw [show (gEntries p w).m1φR'Tw 1 = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1φR'Tw 2
      = (((-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φR'Tw 2) = _
    rw [show (gEntries p w).m1φR'Tw 2 = (((-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_ththR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θθRTw ⬝ᵥ S
      = (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θθRTw 0
      = (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θθRTw 0) = _
    rw [show (gEntries p w).m1θθRTw 0 = (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θθRTw 1
      = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θθRTw 1) = _
    rw [show (gEntries p w).m1θθRTw 1 = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θθRTw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θθRTw 2) = _
    rw [show (gEntries p w).m1θθRTw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_thphR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θφRTw ⬝ᵥ S
      = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θφRTw 0
      = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θφRTw 0) = _
    rw [show (gEntries p w).m1θφRTw 0 = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θφRTw 1
      = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θφRTw 1) = _
    rw [show (gEntries p w).m1θφRTw 1 = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θφRTw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θφRTw 2) = _
    rw [show (gEntries p w).m1θφRTw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_phphR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1φφRTw ⬝ᵥ S
      = (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1φφRTw 0
      = (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φφRTw 0) = _
    rw [show (gEntries p w).m1φφRTw 0 = (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1φφRTw 1
      = (((sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φφRTw 1) = _
    rw [show (gEntries p w).m1φφRTw 1 = (((sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1φφRTw 2
      = (((-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φφRTw 2) = _
    rw [show (gEntries p w).m1φφRTw 2 = (((-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

end GDotBridge

section GloBound

open RationalApprox (sinNum13 cosNum13)

variable {p : Pose ℚ} {w : Fin 2 → ℚ} {wxn wyn : ℤ} {wd : ℕ}
  {S : Fin 3 → ℚ} {s0 s1 s2 : ℤ} {εα εθ₁ εφ₁ : ℚ}

/-- One first-order subtracted term of `fastG`, bounded by its `cdiv`. -/
private lemma eps_term_le (ε : ℚ) (X : ℕ) :
    ε * (((X : ℤ) : ℚ) / 10 ^ 29)
      ≤ ((cdiv (ε.num * (X : ℤ)) ((ε.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < (ε.den : ℤ) * 10 ^ 16 := by positivity
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  calc ε * (((X : ℤ) : ℚ) / 10 ^ 29)
      = ((ε.num * (X : ℤ) : ℤ) : ℚ) / (((ε.den : ℤ) * 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show ε * (((X : ℤ) : ℚ) / 10 ^ 29)
            = (ε.num : ℚ) / (ε.den : ℚ) * (((X : ℤ) : ℚ) / 10 ^ 29) from by
          rw [Rat.num_div_den]]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- One diagonal second-order subtracted term of `fastG`. -/
private lemma eps_sq_term_le (ε : ℚ) (X : ℕ) :
    ε ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29)
      ≤ ((cdiv (ε.num ^ 2 * (X : ℤ)) (2 * (ε.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < 2 * (ε.den : ℤ) ^ 2 * 10 ^ 16 := by positivity
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  calc ε ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29)
      = ((ε.num ^ 2 * (X : ℤ) : ℤ) : ℚ) / ((2 * (ε.den : ℤ) ^ 2 * 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show ε ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29)
            = ((ε.num : ℚ) / (ε.den : ℚ)) ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29) from by
          rw [Rat.num_div_den]]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- One cross second-order subtracted term of `fastG`. -/
private lemma eps_mul_term_le (ε ε' : ℚ) (X : ℕ) :
    ε * ε' * (((X : ℤ) : ℚ) / 10 ^ 29)
      ≤ ((cdiv (ε.num * ε'.num * (X : ℤ)) ((ε.den : ℤ) * (ε'.den : ℤ) * 10 ^ 16) : ℤ) : ℚ)
        / 10 ^ 13 := by
  have hd : (0:ℤ) < (ε.den : ℤ) * (ε'.den : ℤ) * 10 ^ 16 := by positivity
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((ε'.den : ℚ)) ≠ 0 := by positivity
  calc ε * ε' * (((X : ℤ) : ℚ) / 10 ^ 29)
      = ((ε.num * ε'.num * (X : ℤ) : ℤ) : ℚ)
          / (((ε.den : ℤ) * (ε'.den : ℤ) * 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show ε * ε' * (((X : ℤ) : ℚ) / 10 ^ 29)
            = ((ε.num : ℚ) / (ε.den : ℚ)) * ((ε'.num : ℚ) / (ε'.den : ℚ))
              * (((X : ℤ) : ℚ) / 10 ^ 29) from by
          rw [Rat.num_div_den, Rat.num_div_den]]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- The Lagrange-cube subtracted term of `fastG`. -/
private lemma cube_term_le :
    (εα + εθ₁ + εφ₁) ^ 3 / 6
      ≤ ((cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < 6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3 := by positivity
  have hdQ : ((εα.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εθ₁.den : ℚ)) ≠ 0 := by positivity
  have hdQ'' : ((εφ₁.den : ℚ)) ≠ 0 := by positivity
  calc (εα + εθ₁ + εφ₁) ^ 3 / 6
      = (((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13 : ℤ) : ℚ) / ((6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3 : ℤ) : ℚ) / 10 ^ 13 := by
        conv_lhs => rw [← Rat.num_div_den εα, ← Rat.num_div_den εθ₁, ← Rat.num_div_den εφ₁]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- The `κ`-slack subtracted term of `fastG`. -/
private lemma kappa_term_le :
    4 * RationalApprox.κℚ * (1 + (εα + εθ₁ + εφ₁) + (εα + εθ₁ + εφ₁) ^ 2 / 2)
      ≤ ((cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2))
            (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < 2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 := by positivity
  have hdQ : ((εα.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εθ₁.den : ℚ)) ≠ 0 := by positivity
  have hdQ'' : ((εφ₁.den : ℚ)) ≠ 0 := by positivity
  calc 4 * RationalApprox.κℚ * (1 + (εα + εθ₁ + εφ₁) + (εα + εθ₁ + εφ₁) ^ 2 / 2)
      = ((4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2) : ℤ) : ℚ)
          / ((2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show RationalApprox.κℚ = 1 / 10 ^ 10 from rfl]
        conv_lhs => rw [← Rat.num_div_den εα, ← Rat.num_div_den εθ₁, ← Rat.num_div_den εφ₁]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

set_option maxHeartbeats 6400000 in
/-- The conservative integer `glo` of the fast path bounds `fastG` from
below (scaled by `10¹³`). -/
private lemma glo_bound (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) / 10 ^ 16
      - (cdiv (εα.num * (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εα.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num * (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num * (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num ^ 2 * (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) (2 * (εα.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εα.num * εθ₁.num * (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εα.den : ℤ) * (εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num * εφ₁.num * (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εα.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num ^ 2 * (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) (2 * (εθ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εθ₁.num * εφ₁.num * (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εθ₁.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num ^ 2 * (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) (2 * (εφ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3)
        + cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2)) (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2)) : ℤ) : ℚ) / 10 ^ 13)
      ≤ fastG (gEntriesR p w) εα εθ₁ εφ₁ S := by
  have hd1 := gdot_R (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd2 := gdot_R' (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd3 := gdot_thR (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd4 := gdot_phR (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd5 := gdot_thR' (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd6 := gdot_phR' (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd7 := gdot_ththR (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd8 := gdot_thphR (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hd9 := gdot_phphR (p := p) hwd hw0 hw1 hS0 hS1 hS2
  have hsplit : (((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) / 10 ^ 16
      - (cdiv (εα.num * (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εα.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num * (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num * (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num ^ 2 * (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) (2 * (εα.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εα.num * εθ₁.num * (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εα.den : ℤ) * (εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num * εφ₁.num * (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εα.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num ^ 2 * (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) (2 * (εθ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εθ₁.num * εφ₁.num * (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εθ₁.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num ^ 2 * (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) (2 * (εφ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3)
        + cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2)) (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2)) : ℤ) : ℚ) / 10 ^ 13)
      = (((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) / 10 ^ 16 : ℤ) : ℚ)) / 10 ^ 13
        - (((cdiv (εα.num * (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εα.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εθ₁.num * (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εθ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εφ₁.num * (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εφ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εα.num ^ 2 * (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) (2 * (εα.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εα.num * εθ₁.num * (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εα.den : ℤ) * (εθ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εα.num * εφ₁.num * (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) ((εα.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εθ₁.num ^ 2 * (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) (2 * (εθ₁.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εθ₁.num * εφ₁.num * (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs : ℤ)) ((εθ₁.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (εφ₁.num ^ 2 * (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs : ℤ)) (2 * (εφ₁.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3) : ℤ) : ℚ) / 10 ^ 13 + ((cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2)) (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2) : ℤ) : ℚ) / 10 ^ 13) := by
    push_cast
    ring
  have hlead : (((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) / 10 ^ 16 : ℤ) : ℚ)) / 10 ^ 13
      ≤ ((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) : ℤ) : ℚ) / 10 ^ 29 := by
    calc (((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) / 10 ^ 16 : ℤ) : ℚ)) / 10 ^ 13
        ≤ (((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) : ℤ) : ℚ) / ((10 ^ 16 : ℤ) : ℚ)) / 10 ^ 13 := by
          gcongr
          exact ediv_le (by norm_num)
      _ = ((((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2) : ℤ) : ℚ) / 10 ^ 29 := by
          rw [div_div]
          norm_num
  have ht0 := eps_term_le εα (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs)
  have ht1 := eps_term_le εθ₁ (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs)
  have ht2 := eps_term_le εφ₁ (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs)
  have ht3 := eps_sq_term_le εα (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs)
  have ht4 := eps_mul_term_le εα εθ₁ (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs)
  have ht5 := eps_mul_term_le εα εφ₁ (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs)
  have ht6 := eps_sq_term_le εθ₁ (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs)
  have ht7 := eps_mul_term_le εθ₁ εφ₁ (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1).natAbs)
  have ht8 := eps_sq_term_le εφ₁ (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2).natAbs)
  have ht9 := cube_term_le (εα := εα) (εθ₁ := εθ₁) (εφ₁ := εφ₁)
  have ht10 := kappa_term_le (εα := εα) (εθ₁ := εθ₁) (εφ₁ := εφ₁)
  unfold fastG
  rw [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9]
  rw [abs_intCast_div29, abs_intCast_div29, abs_intCast_div29, abs_intCast_div29,
    abs_intCast_div29, abs_intCast_div29, abs_intCast_div29, abs_intCast_div29,
    abs_intCast_div29]
  simp only [Int.abs_eq_natAbs]
  rw [hsplit]
  linarith [hlead, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]

end GloBound

section HBounds

variable {εθ₂ εφ₂ : ℚ}

/-- `|·|` through a scale-`10¹³` integer fraction. -/
private lemma abs_intCast_div13 (n : ℤ) :
    |(n : ℚ) / 10 ^ 13| = ((|n| : ℤ) : ℚ) / 10 ^ 13 := by
  rw [abs_div, abs_of_pos (by positivity : (0:ℚ) < (10:ℚ) ^ 13)]
  push_cast
  ring_nf

/-- The pipeline `kRhi` bounds `(εθ₂+εφ₂)³/6 + kappaTerm` from above. -/
private lemma kR_bound :
    ((εθ₂ + εφ₂) ^ 3 / 6
        + 3 * RationalApprox.κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂) ^ 2 / 2)) * 10 ^ 13
      ≤ ((cdiv ((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13) (6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3)
          + cdiv (3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2))
              (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) : ℤ) : ℚ) := by
  have hdQ : ((εθ₂.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εφ₂.den : ℚ)) ≠ 0 := by positivity
  have h1 : (εθ₂ + εφ₂) ^ 3 / 6 * 10 ^ 13
      ≤ ((cdiv ((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13) (6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3) : ℤ) : ℚ) := by
    calc (εθ₂ + εφ₂) ^ 3 / 6 * 10 ^ 13
        = (((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13 : ℤ) : ℚ) / ((6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3 : ℤ) : ℚ) := by
          conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
          push_cast
          field_simp
          ring
      _ ≤ _ := le_cdiv (by positivity)
  have h2 : 3 * RationalApprox.κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂) ^ 2 / 2) * 10 ^ 13
      ≤ ((cdiv (3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2))
            (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) : ℤ) : ℚ) := by
    calc 3 * RationalApprox.κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂) ^ 2 / 2) * 10 ^ 13
        = ((3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2) : ℤ) : ℚ)
            / ((2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 : ℤ) : ℚ) := by
          rw [show RationalApprox.κℚ = 1 / 10 ^ 10 from rfl]
          conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
          push_cast
          field_simp
          ring
      _ ≤ _ := le_cdiv (by positivity)
  push_cast
  linarith

/-- The pipeline `eθhi`/`eφhi` bound the radii from above. -/
private lemma eps13_bound (ε : ℚ) :
    ε * 10 ^ 13 ≤ ((cdiv (ε.num * 10 ^ 13) (ε.den : ℤ) : ℤ) : ℚ) := by
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  calc ε * 10 ^ 13 = ((ε.num * 10 ^ 13 : ℤ) : ℚ) / (((ε.den : ℤ) : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den ε]
        push_cast
        field_simp
        norm_num
    _ ≤ _ := le_cdiv (by exact_mod_cast ε.pos)

/-- The pipeline `soHi` bounds `soBound` from above, given the scale-`10¹³`
integer forms of the second-order scalars. -/
private lemma so_bound {e : HScalars} {d0 d1 e0 e1 f0 f1 f2 : ℤ}
    (hd0 : e.d0 = (d0 : ℚ) / 10 ^ 13) (hd1 : e.d1 = (d1 : ℚ) / 10 ^ 13)
    (hd2 : e.d2 = 0)
    (he0 : e.e0 = (e0 : ℚ) / 10 ^ 13) (he1 : e.e1 = (e1 : ℚ) / 10 ^ 13)
    (he2 : e.e2 = 0)
    (hf0 : e.f0 = (f0 : ℚ) / 10 ^ 13) (hf1 : e.f1 = (f1 : ℚ) / 10 ^ 13)
    (hf2 : e.f2 = (f2 : ℚ) / 10 ^ 13) :
    soBound e εθ₂ εφ₂ * 10 ^ 13
      ≤ ((cdiv (εθ₂.num ^ 2 * (max (d0.natAbs : ℤ) (d1.natAbs : ℤ)) * (εφ₂.den : ℤ) ^ 2
            + 2 * εθ₂.num * εφ₂.num * (max (e0.natAbs : ℤ) (e1.natAbs : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ))
            + εφ₂.num ^ 2 * (max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)))
                * (εθ₂.den : ℤ) ^ 2)
          (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) : ℤ) : ℚ) := by
  have hdQ : ((εθ₂.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εφ₂.den : ℚ)) ≠ 0 := by positivity
  have hmaxd : max |e.d0| (max |e.d1| |e.d2|)
      = ((max (d0.natAbs : ℤ) (d1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hd0, hd1, hd2, abs_intCast_div13, abs_intCast_div13, abs_zero]
    rw [show max (((|d1| : ℤ) : ℚ) / 10 ^ 13) 0 = ((|d1| : ℤ) : ℚ) / 10 ^ 13 from
      max_eq_left (by positivity)]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have hmaxe : max |e.e0| (max |e.e1| |e.e2|)
      = ((max (e0.natAbs : ℤ) (e1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [he0, he1, he2, abs_intCast_div13, abs_intCast_div13, abs_zero]
    rw [show max (((|e1| : ℤ) : ℚ) / 10 ^ 13) 0 = ((|e1| : ℤ) : ℚ) / 10 ^ 13 from
      max_eq_left (by positivity)]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have hmaxf : max |e.f0| (max |e.f1| |e.f2|)
      = ((max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hf0, hf1, hf2, abs_intCast_div13, abs_intCast_div13, abs_intCast_div13]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13),
      max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max, ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  unfold soBound
  rw [hmaxd, hmaxe, hmaxf]
  calc 1 / 2 * (εθ₂ ^ 2 * (((max (d0.natAbs : ℤ) (d1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13)
        + 2 * (εθ₂ * εφ₂) * (((max (e0.natAbs : ℤ) (e1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13)
        + εφ₂ ^ 2 * (((max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)) : ℤ) : ℚ)
            / 10 ^ 13)) * 10 ^ 13
      = ((εθ₂.num ^ 2 * (max (d0.natAbs : ℤ) (d1.natAbs : ℤ)) * (εφ₂.den : ℤ) ^ 2
            + 2 * εθ₂.num * εφ₂.num * (max (e0.natAbs : ℤ) (e1.natAbs : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ))
            + εφ₂.num ^ 2 * (max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)))
                * (εθ₂.den : ℤ) ^ 2 : ℤ) : ℚ)
          / ((2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
        push_cast
        field_simp
    _ ≤ _ := le_cdiv (by positivity)

/-- The pipeline `foHi` summand bounds `foBound` from above. -/
private lemma fo_bound {e : HScalars} {b0 b1 c0 c1 c2 : ℤ}
    (hb0 : e.b0 = (b0 : ℚ) / 10 ^ 13) (hb1 : e.b1 = (b1 : ℚ) / 10 ^ 13)
    (hb2 : e.b2 = 0)
    (hc0 : e.c0 = (c0 : ℚ) / 10 ^ 13) (hc1 : e.c1 = (c1 : ℚ) / 10 ^ 13)
    (hc2 : e.c2 = (c2 : ℚ) / 10 ^ 13) :
    foBound e εθ₂ εφ₂ * 10 ^ 13
      ≤ ((cdiv (εθ₂.num * (max (b0.natAbs : ℤ) (b1.natAbs : ℤ)) * (εφ₂.den : ℤ)
            + εφ₂.num * (max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)))
                * (εθ₂.den : ℤ))
          ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) : ℤ) : ℚ) := by
  have hdQ : ((εθ₂.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εφ₂.den : ℚ)) ≠ 0 := by positivity
  have hmaxb : max |e.b0| (max |e.b1| |e.b2|)
      = ((max (b0.natAbs : ℤ) (b1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hb0, hb1, hb2, abs_intCast_div13, abs_intCast_div13, abs_zero]
    rw [show max (((|b1| : ℤ) : ℚ) / 10 ^ 13) 0 = ((|b1| : ℤ) : ℚ) / 10 ^ 13 from
      max_eq_left (by positivity)]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have hmaxc : max |e.c0| (max |e.c1| |e.c2|)
      = ((max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hc0, hc1, hc2, abs_intCast_div13, abs_intCast_div13, abs_intCast_div13]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13),
      max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max, ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  unfold foBound
  rw [hmaxb, hmaxc]
  calc (εθ₂ * (((max (b0.natAbs : ℤ) (b1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13)
        + εφ₂ * (((max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)) : ℤ) : ℚ)
            / 10 ^ 13)) * 10 ^ 13
      = ((εθ₂.num * (max (b0.natAbs : ℤ) (b1.natAbs : ℤ)) * (εφ₂.den : ℤ)
            + εφ₂.num * (max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)))
                * (εθ₂.den : ℤ) : ℤ) : ℚ)
          / ((((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
        push_cast
        field_simp
    _ ≤ _ := le_cdiv (by positivity)

end HBounds

/-- Unroll a true `natTierLoop` into per-vertex `natTierBody` facts. -/
private lemma natTierLoop_forall
    {bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC D0 D1 D2 fsD E0 E1 E2 fsE
     F0 F1 F2 fsF g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 : ℕ} :
    ∀ {n : ℕ}, natTierLoop bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
      D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
      g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 n = true →
    ∀ j, j < n →
      (let v := Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)
       natTierBody A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
         D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
         g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3
         (Nat.land v (2 ^ 57 - 1)) (Nat.land (Nat.shiftRight v 57) (2 ^ 57 - 1))
         (Nat.shiftRight v 114)) = true := by
  intro n
  induction n with
  | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro h j hj
    rw [natTierLoop, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · exact ih h.2 j h'
    · exact h.1

end Gℚ_gt_maxHℚ

open Gℚ_gt_maxHℚ in
/-- One-sided all-`Nat` fast path for `Gℚ_gt_maxHℚ_check` (see the section
docstring). `bigT` is the packed vertex table covering flat indices
`[0, nV)`, `sflat` the flat index of `S`, and `w = ![wxn/wd, wyn/wd]`. -/
def Gℚ_gt_maxHℚ_fastNat (bigT nV sflat : ℕ) (p : Pose ℚ)
    (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (wxn wyn : ℤ) (wd : ℕ) : Bool :=
  -- trig integer cores (scale 10¹³)
  let st2 := RationalApprox.sinNum13 p.θ₂
  let ct2 := RationalApprox.cosNum13 p.θ₂
  let sp2 := RationalApprox.sinNum13 p.φ₂
  let cp2 := RationalApprox.cosNum13 p.φ₂
  let st1 := RationalApprox.sinNum13 p.θ₁
  let ct1 := RationalApprox.cosNum13 p.θ₁
  let sp1 := RationalApprox.sinNum13 p.φ₁
  let cp1 := RationalApprox.cosNum13 p.φ₁
  let sa := RationalApprox.sinNum13 p.α
  let ca := RationalApprox.cosNum13 p.α
  let wdZ : ℤ := wd
  -- H-side entry numerators over 10²⁶·wd, rounded to scale 10¹³ (= hEntriesR)
  let dh : ℤ := 10 ^ 13 * wdZ
  let ctcp := ct2 * cp2
  let stcp := st2 * cp2
  let Aa0 := -(st2 * wxn) * 10 ^ 13 - ctcp * wyn
  let Aa1 := ct2 * wxn * 10 ^ 13 - stcp * wyn
  let Aa2 := sp2 * wyn * 10 ^ 13
  let Ab0 := -(ct2 * wxn) * 10 ^ 13 + stcp * wyn
  let Ac0 := ct2 * sp2 * wyn
  let Ac1 := st2 * sp2 * wyn
  let Ac2 := cp2 * wyn * 10 ^ 13
  let a0N := Aa0 / dh
  let a1N := Aa1 / dh
  let a2N := Aa2 / dh
  let b0N := Ab0 / dh
  let b1N := Aa0 / dh
  let c0N := Ac0 / dh
  let c1N := Ac1 / dh
  let c2N := Ac2 / dh
  let d0N := (-Aa0) / dh
  let d1N := Ab0 / dh
  let e0N := (-Ac1) / dh
  let e1N := Ac0 / dh
  let f0N := (ctcp * wyn) / dh
  let f1N := (stcp * wyn) / dh
  let f2N := (-Aa2) / dh
  -- G-side: Rᵀw / R'ᵀw at scale 10¹³·wd, entries over 10³⁹·wd → scale 10¹³
  let dg : ℤ := 10 ^ 26 * wdZ
  let u0 := ca * wxn + sa * wyn
  let u1 := -(sa * wxn) + ca * wyn
  let ctcp1 := ct1 * cp1
  let stcp1 := st1 * cp1
  let r0N := (-(st1 * u0) * 10 ^ 13 - ctcp1 * u1) / dg
  let r1N := (ct1 * u0 * 10 ^ 13 - stcp1 * u1) / dg
  let r2N := (sp1 * u1 * 10 ^ 13) / dg
  let s0N := (-(st1 * u1) * 10 ^ 13 + ctcp1 * u0) / dg
  let s1N := (ct1 * u1 * 10 ^ 13 + stcp1 * u0) / dg
  let s2N := (-(sp1 * u0) * 10 ^ 13) / dg
  let t0N := (-(ct1 * u0) * 10 ^ 13 + stcp1 * u1) / dg
  let t1N := (-(st1 * u0) * 10 ^ 13 - ctcp1 * u1) / dg
  let u0N' := (ct1 * sp1 * u1) / dg
  let u1N' := (st1 * sp1 * u1) / dg
  let u2N' := (cp1 * u1 * 10 ^ 13) / dg
  let v0N := (-(ct1 * u1) * 10 ^ 13 - stcp1 * u0) / dg
  let v1N := (-(st1 * u1) * 10 ^ 13 + ctcp1 * u0) / dg
  let w0N := (-(ct1 * sp1 * u0)) / dg
  let w1N := (-(st1 * sp1 * u0)) / dg
  let w2N := (-(cp1 * u0) * 10 ^ 13) / dg
  let x0N := (st1 * u0 * 10 ^ 13 + ctcp1 * u1) / dg
  let x1N := (-(ct1 * u0) * 10 ^ 13 + stcp1 * u1) / dg
  let y0N := (-(st1 * sp1 * u1)) / dg
  let y1N := (ct1 * sp1 * u1) / dg
  let z0N := (ctcp1 * u1) / dg
  let z1N := (stcp1 * u1) / dg
  let z2N := (-(sp1 * u1) * 10 ^ 13) / dg
  -- S coordinates (scale 10¹⁶) from the packed table
  let m57 : ℕ := 2 ^ 57 - 1
  let sv := (bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)
  let S0 : ℤ := ((sv &&& m57 : ℕ) : ℤ) - 2 ^ 56
  let S1 : ℤ := (((sv >>> 57) &&& m57 : ℕ) : ℤ) - 2 ^ 56
  let S2 : ℤ := ((sv >>> 114 : ℕ) : ℤ) - 2 ^ 56
  -- the nine G dots (scale 10²⁹)
  let dR := r0N * S0 + r1N * S1 + r2N * S2
  let dR' := (s0N * S0 + s1N * S1 + s2N * S2).natAbs
  let dθR := (t0N * S0 + t1N * S1).natAbs
  let dφR := (u0N' * S0 + u1N' * S1 + u2N' * S2).natAbs
  let dθR' := (v0N * S0 + v1N * S1).natAbs
  let dφR' := (w0N * S0 + w1N * S1 + w2N * S2).natAbs
  let dθθR := (x0N * S0 + x1N * S1).natAbs
  let dθφR := (y0N * S0 + y1N * S1).natAbs
  let dφφR := (z0N * S0 + z1N * S1 + z2N * S2).natAbs
  let dRabs : ℤ := dR.natAbs
  -- g lower bound at scale 10¹³: leading dot floored, every subtracted
  -- term ceiled
  let εαn := εα.num
  let εαd : ℤ := εα.den
  let εθ₁n := εθ₁.num
  let εθ₁d : ℤ := εθ₁.den
  let εφ₁n := εφ₁.num
  let εφ₁d : ℤ := εφ₁.den
  let En := εαn * (εθ₁d * εφ₁d) + εθ₁n * (εαd * εφ₁d) + εφ₁n * (εαd * εθ₁d)
  let Ed := εαd * (εθ₁d * εφ₁d)
  let glo := dR / 10 ^ 16
    - (cdiv (εαn * dR') (εαd * 10 ^ 16)
      + cdiv (εθ₁n * dθR) (εθ₁d * 10 ^ 16)
      + cdiv (εφ₁n * dφR) (εφ₁d * 10 ^ 16)
      + cdiv (εαn ^ 2 * dRabs) (2 * εαd ^ 2 * 10 ^ 16)
      + cdiv (εαn * εθ₁n * dθR') (εαd * εθ₁d * 10 ^ 16)
      + cdiv (εαn * εφ₁n * dφR') (εαd * εφ₁d * 10 ^ 16)
      + cdiv (εθ₁n ^ 2 * dθθR) (2 * εθ₁d ^ 2 * 10 ^ 16)
      + cdiv (εθ₁n * εφ₁n * dθφR) (εθ₁d * εφ₁d * 10 ^ 16)
      + cdiv (εφ₁n ^ 2 * dφφR) (2 * εφ₁d ^ 2 * 10 ^ 16)
      + cdiv (En ^ 3 * 10 ^ 13) (6 * Ed ^ 3)
      + cdiv (4000 * (2 * Ed ^ 2 + 2 * En * Ed + En ^ 2)) (2 * Ed ^ 2))
  -- H-side row constants, rounded up at scale 10¹³
  let εθ₂n := εθ₂.num
  let εθ₂d : ℤ := εθ₂.den
  let εφ₂n := εφ₂.num
  let εφ₂d : ℤ := εφ₂.den
  let E2n := εθ₂n * εφ₂d + εφ₂n * εθ₂d
  let E2d := εθ₂d * εφ₂d
  let kRhi := cdiv (E2n ^ 3 * 10 ^ 13) (6 * E2d ^ 3)
    + cdiv (3000 * (2 * E2d ^ 2 + 2 * E2n * E2d + E2n ^ 2)) (2 * E2d ^ 2)
  let maxbN : ℤ := max b0N.natAbs b1N.natAbs
  let maxcN : ℤ := max c0N.natAbs (max c1N.natAbs c2N.natAbs)
  let maxdN : ℤ := max d0N.natAbs d1N.natAbs
  let maxeN : ℤ := max e0N.natAbs e1N.natAbs
  let maxfN : ℤ := max f0N.natAbs (max f1N.natAbs f2N.natAbs)
  let soHi := cdiv (εθ₂n ^ 2 * maxdN * εφ₂d ^ 2 + 2 * εθ₂n * εφ₂n * maxeN * E2d
      + εφ₂n ^ 2 * maxfN * εθ₂d ^ 2) (2 * E2d ^ 2)
  let fsHi := soHi + cdiv (εθ₂n * maxbN * εφ₂d + εφ₂n * maxcN * εθ₂d) E2d
  let eθhi := cdiv (εθ₂n * 10 ^ 13) εθ₂d
  let eφhi := cdiv (εφ₂n * 10 ^ 13) εφ₂d
  -- guards, then the pure-Nat loop
  decide (0 < wd) && decide (0 ≤ εαn) && decide (0 ≤ εθ₁n) && decide (0 ≤ εφ₁n) &&
  decide (0 ≤ εθ₂n) && decide (0 ≤ εφ₂n) && decide (0 < glo) &&
  offOk a0N && offOk a1N && offOk a2N &&
  offOk b0N && offOk b1N &&
  offOk c0N && offOk c1N && offOk c2N &&
  offOk d0N && offOk d1N &&
  offOk e0N && offOk e1N &&
  offOk f0N && offOk f1N && offOk f2N &&
  (let A0 := (a0N + 2 ^ 47).toNat
   let A1 := (a1N + 2 ^ 47).toNat
   let A2 := (a2N + 2 ^ 47).toNat
   let B0 := (b0N + 2 ^ 47).toNat
   let B1 := (b1N + 2 ^ 47).toNat
   let B2 : ℕ := 2 ^ 47
   let C0 := (c0N + 2 ^ 47).toNat
   let C1 := (c1N + 2 ^ 47).toNat
   let C2 := (c2N + 2 ^ 47).toNat
   let D0 := (d0N + 2 ^ 47).toNat
   let D1 := (d1N + 2 ^ 47).toNat
   let D2 : ℕ := 2 ^ 47
   let E0 := (e0N + 2 ^ 47).toNat
   let E1 := (e1N + 2 ^ 47).toNat
   let E2 : ℕ := 2 ^ 47
   let F0 := (f0N + 2 ^ 47).toNat
   let F1 := (f1N + 2 ^ 47).toNat
   let F2 := (f2N + 2 ^ 47).toNat
   let gloN := glo.toNat
   let kRN := kRhi.toNat
   let fsBh := fsHi.toNat
   let soB13 := soHi.toNat * 10 ^ 13
   let eθN := eθhi.toNat
   let eφN := eφhi.toNat
   natTierLoop bigT A0 A1 A2 (2 ^ 56 * (A0 + A1 + A2))
     B0 B1 B2 (2 ^ 56 * (B0 + B1 + B2))
     C0 C1 C2 (2 ^ 56 * (C0 + C1 + C2))
     D0 D1 D2 (2 ^ 56 * (D0 + D1 + D2))
     E0 E1 E2 (2 ^ 56 * (E0 + E1 + E2))
     F0 F1 F2 (2 ^ 56 * (F0 + F1 + F2))
     (gloN * 10 ^ 16) (gloN * 10 ^ 29) (2 * gloN * 10 ^ 42)
     fsBh soB13 (kRN * 10 ^ 16) (kRN * 10 ^ 29) (2 * kRN * 10 ^ 42)
     eθN eφN (eθN ^ 2) (2 * eθN * eφN) (eφN ^ 2) nV)

open Gℚ_gt_maxHℚ in
set_option maxHeartbeats 6400000 in
/-- **Soundness of the all-`Nat` fast path**: if `Gℚ_gt_maxHℚ_fastNat` accepts,
the ℚ tiered check accepts. `bigT` is an arbitrary packed vertex table; the
`hfield`/`hS` hypotheses state (in exactly the shapes the fast path reads)
that its fields are the offset-encoded coordinates of `poly.v ∘ ix` and `S`,
and `hcover` that `ix` covers `ι` below `nV`. -/
theorem Gℚ_gt_maxHℚ_fastNat_sound {ι : Type} [Fintype ι] [DecidableEq ι]
    (bigT nV sflat : ℕ) (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ)
    (wxn wyn : ℤ) (wd : ℕ)
    (S : Fin 3 → ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (ix : ℕ → ι)
    (hcover : ∀ k : ι, ∃ j, j < nV ∧ ix j = k)
    (hfield : ∀ j, j < nV →
      (let v := Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)
       ((Nat.land v (2 ^ 57 - 1) : ℕ) : ℚ) = poly.v (ix j) 0 * 10 ^ 16 + 2 ^ 56
        ∧ ((Nat.land (Nat.shiftRight v 57) (2 ^ 57 - 1) : ℕ) : ℚ)
            = poly.v (ix j) 1 * 10 ^ 16 + 2 ^ 56
        ∧ ((Nat.shiftRight v 114 : ℕ) : ℚ) = poly.v (ix j) 2 * 10 ^ 16 + 2 ^ 56))
    (hS0 : S 0 = (((((bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)) &&& (2 ^ 57 - 1) : ℕ) : ℤ)
        - 2 ^ 56 : ℤ) / 10 ^ 16)
    (hS1 : S 1 = ((((((bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)) >>> 57) &&& (2 ^ 57 - 1)
        : ℕ) : ℤ) - 2 ^ 56 : ℤ) / 10 ^ 16)
    (hS2 : S 2 = (((((bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)) >>> 114 : ℕ) : ℤ)
        - 2 ^ 56 : ℤ) / 10 ^ 16)
    (h : Gℚ_gt_maxHℚ_fastNat bigT nV sflat p εα εθ₁ εφ₁ εθ₂ εφ₂ wxn wyn wd = true) :
    Gℚ_gt_maxHℚ_check p εα εθ₁ εφ₁ εθ₂ εφ₂ S poly w = true := by
  unfold Gℚ_gt_maxHℚ_fastNat at h
  simp only [offOk, Bool.and_eq_true, and_assoc, decide_eq_true_eq] at h
  obtain ⟨hwd, hεαn, hεθ₁n, hεφ₁n, hεθ₂n, hεφ₂n, hglo0, hoa0, hoa1, hoa2,
    hob0, hob1, hoc0, hoc1, hoc2, hod0, hod1, hoe0, hoe1, hof0, hof1, hof2,
    hloop⟩ := h
  have hεα : 0 ≤ εα := Rat.num_nonneg.mp hεαn
  have hεθ₁' : 0 ≤ εθ₁ := Rat.num_nonneg.mp hεθ₁n
  have hεφ₁' : 0 ≤ εφ₁ := Rat.num_nonneg.mp hεφ₁n
  have hεθ₂' : 0 ≤ εθ₂ := Rat.num_nonneg.mp hεθ₂n
  have hεφ₂' : 0 ≤ εφ₂ := Rat.num_nonneg.mp hεφ₂n
  unfold Gℚ_gt_maxHℚ_check
  simp only [decide_eq_true_eq]
  intro k
  obtain ⟨j, hj, rfl⟩ := hcover k
  have hbody := natTierLoop_forall hloop j hj
  obtain ⟨hf0, hf1, hf2⟩ := hfield j hj
  have hwdQpos : 0 < wd := hwd
  -- vertex coordinate links
  have hp0 : poly.v (ix j) 0
      = (((((Nat.land (Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)) (2 ^ 57 - 1) : ℕ) : ℤ) - 2 ^ 56 : ℤ) : ℚ)) / 10 ^ 16 := by
    push_cast at hf0 ⊢
    linarith
  have hp1 : poly.v (ix j) 1
      = (((((Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)) 57) (2 ^ 57 - 1) : ℕ) : ℤ) - 2 ^ 56 : ℤ) : ℚ)) / 10 ^ 16 := by
    push_cast at hf1 ⊢
    linarith
  have hp2 : poly.v (ix j) 2
      = (((((Nat.shiftRight (Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)) 114 : ℕ) : ℤ) - 2 ^ 56 : ℤ) : ℚ)) / 10 ^ 16 := by
    push_cast at hf2 ⊢
    linarith
  -- nonnegativity of the rounded-up row constants (for the `toNat` links)
  have hE2n : (0:ℤ) ≤ (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) :=
    add_nonneg (mul_nonneg hεθ₂n (by positivity)) (mul_nonneg hεφ₂n (by positivity))
  have hE2d : (0:ℤ) < (εθ₂.den : ℤ) * (εφ₂.den : ℤ) := by positivity
  have hkRhi0 : (0:ℤ) ≤ cdiv ((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13)
        (6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3)
      + cdiv (3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2
          + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2))
        (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) :=
    add_nonneg
      (cdiv_nonneg (mul_nonneg (pow_nonneg hE2n 3) (by norm_num)) (by positivity))
      (cdiv_nonneg
        (mul_nonneg (by norm_num)
          (add_nonneg (add_nonneg (by positivity)
            (mul_nonneg (mul_nonneg (by norm_num) hE2n) hE2d.le)) (pow_nonneg hE2n 2)))
        (by positivity))
  have heθhi0 : (0:ℤ) ≤ cdiv (εθ₂.num * 10 ^ 13) (εθ₂.den : ℤ) :=
    cdiv_nonneg (mul_nonneg hεθ₂n (by norm_num)) (by exact_mod_cast εθ₂.pos)
  have heφhi0 : (0:ℤ) ≤ cdiv (εφ₂.num * 10 ^ 13) (εφ₂.den : ℤ) :=
    cdiv_nonneg (mul_nonneg hεφ₂n (by norm_num)) (by exact_mod_cast εφ₂.pos)
  refine natTierBody_sound (b2N := 0) (d2N := 0) (e2N := 0)
    (hentry_a0 (p := p) hwd hw0 hw1) (hentry_a1 (p := p) hwd hw0 hw1)
    (hentry_a2 (p := p) hwd hw0 hw1)
    (hentry_b0 (p := p) hwd hw0 hw1) (hentry_b1 (p := p) hwd hw0 hw1) ?hb2
    (hentry_c0 (p := p) hwd hw0 hw1) (hentry_c1 (p := p) hwd hw0 hw1)
    (hentry_c2 (p := p) hwd hw0 hw1)
    (hentry_d0 (p := p) hwd hw0 hw1) (hentry_d1 (p := p) hwd hw0 hw1) ?hd2
    (hentry_e0 (p := p) hwd hw0 hw1) (hentry_e1 (p := p) hwd hw0 hw1) ?he2
    (hentry_f0 (p := p) hwd hw0 hw1) (hentry_f1 (p := p) hwd hw0 hw1)
    (hentry_f2 (p := p) hwd hw0 hw1)
    (by ring) (by ring) (by ring)
    hp0 hp1 hp2
    (Int.toNat_of_nonneg hoa0) (Int.toNat_of_nonneg hoa1) (Int.toNat_of_nonneg hoa2)
    (Int.toNat_of_nonneg hob0) (Int.toNat_of_nonneg hob1) ?hB2
    (Int.toNat_of_nonneg hoc0) (Int.toNat_of_nonneg hoc1) (Int.toNat_of_nonneg hoc2)
    (Int.toNat_of_nonneg hod0) (Int.toNat_of_nonneg hod1) ?hD2
    (Int.toNat_of_nonneg hoe0) (Int.toNat_of_nonneg hoe1) ?hE2
    (Int.toNat_of_nonneg hof0) (Int.toNat_of_nonneg hof1) (Int.toNat_of_nonneg hof2)
    (glo_bound hwd hw0 hw1 hS0 hS1 hS2) rfl (kR_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂)) ?hfs
    (so_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂)
      (hentry_d0 (p := p) hwd hw0 hw1) (hentry_d1 (p := p) hwd hw0 hw1) ?hd2'
      (hentry_e0 (p := p) hwd hw0 hw1) (hentry_e1 (p := p) hwd hw0 hw1) ?he2'
      (hentry_f0 (p := p) hwd hw0 hw1) (hentry_f1 (p := p) hwd hw0 hw1)
      (hentry_f2 (p := p) hwd hw0 hw1))
    (eps13_bound εθ₂) (eps13_bound εφ₂) hεθ₂' hεφ₂'
    rfl rfl rfl rfl rfl rfl
    ?hg16 ?hg29 ?hg42
    (Int.toNat_of_nonneg ?hfsHi0) ?hsoB13
    ?hkR16 ?hkR29 ?hkR42
    (Int.toNat_of_nonneg heθhi0) (Int.toNat_of_nonneg heφhi0)
    ?hq1 ?hq2 ?hq3
    hbody
  case hb2 =>
    show RationalApprox.round13 ((hEntries p w).m2θtw 2) = _
    rw [show (hEntries p w).m2θtw 2 = 0 from by
      simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  case hd2 =>
    show RationalApprox.round13 ((hEntries p w).m2θθtw 2) = _
    rw [show (hEntries p w).m2θθtw 2 = 0 from by
      simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  case he2 =>
    show RationalApprox.round13 ((hEntries p w).m2θφtw 2) = _
    rw [show (hEntries p w).m2θφtw 2 = 0 from by
      simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  case hd2' =>
    show RationalApprox.round13 ((hEntries p w).m2θθtw 2) = _
    rw [show (hEntries p w).m2θθtw 2 = 0 from by
      simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  case he2' =>
    show RationalApprox.round13 ((hEntries p w).m2θφtw 2) = _
    rw [show (hEntries p w).m2θφtw 2 = 0 from by
      simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  case hB2 => norm_num
  case hD2 => norm_num
  case hE2 => norm_num
  case hfs =>
    have h1 := fo_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂)
      (hentry_b0 (p := p) hwd hw0 hw1) (hentry_b1 (p := p) hwd hw0 hw1)
      (by
        show RationalApprox.round13 ((hEntries p w).m2θtw 2) = _
        rw [show (hEntries p w).m2θtw 2 = 0 from by
          simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
        unfold RationalApprox.round13
        norm_num)
      (hentry_c0 (p := p) hwd hw0 hw1) (hentry_c1 (p := p) hwd hw0 hw1)
      (hentry_c2 (p := p) hwd hw0 hw1)
    have h2 := so_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂)
      (hentry_d0 (p := p) hwd hw0 hw1) (hentry_d1 (p := p) hwd hw0 hw1)
      (by
        show RationalApprox.round13 ((hEntries p w).m2θθtw 2) = _
        rw [show (hEntries p w).m2θθtw 2 = 0 from by
          simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
        unfold RationalApprox.round13
        norm_num)
      (hentry_e0 (p := p) hwd hw0 hw1) (hentry_e1 (p := p) hwd hw0 hw1)
      (by
        show RationalApprox.round13 ((hEntries p w).m2θφtw 2) = _
        rw [show (hEntries p w).m2θφtw 2 = 0 from by
          simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
        unfold RationalApprox.round13
        norm_num)
      (hentry_f0 (p := p) hwd hw0 hw1) (hentry_f1 (p := p) hwd hw0 hw1)
      (hentry_f2 (p := p) hwd hw0 hw1)
    push_cast
    push_cast at h1 h2
    linarith
  case hfsHi0 =>
    refine add_nonneg ?_ ?_
    · exact cdiv_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (pow_nonneg hεθ₂n 2)
              (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity))
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεθ₂n) hεφ₂n)
              (le_max_iff.mpr (Or.inl (by positivity)))) hE2d.le))
          (mul_nonneg (mul_nonneg (pow_nonneg hεφ₂n 2)
            (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity)))
        (by positivity)
    · exact cdiv_nonneg
        (add_nonneg
          (mul_nonneg (mul_nonneg hεθ₂n (le_max_iff.mpr (Or.inl (by positivity))))
            (by positivity))
          (mul_nonneg (mul_nonneg hεφ₂n (le_max_iff.mpr (Or.inl (by positivity))))
            (by positivity)))
        hE2d
  case hsoB13 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg ?_]
    · push_cast
      ring
    · exact cdiv_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (pow_nonneg hεθ₂n 2)
              (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity))
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεθ₂n) hεφ₂n)
              (le_max_iff.mpr (Or.inl (by positivity)))) hE2d.le))
          (mul_nonneg (mul_nonneg (pow_nonneg hεφ₂n 2)
            (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity)))
        (by positivity)
  case hg16 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hglo0.le]
    push_cast
    ring
  case hg29 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hglo0.le]
    push_cast
    ring
  case hg42 =>
    rw [Nat.cast_mul, Nat.cast_mul, Int.toNat_of_nonneg hglo0.le]
    push_cast
    ring
  case hkR16 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hkRhi0]
    push_cast
    ring
  case hkR29 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hkRhi0]
    push_cast
    ring
  case hkR42 =>
    rw [Nat.cast_mul, Nat.cast_mul, Int.toNat_of_nonneg hkRhi0]
    push_cast
    ring
  case hq1 =>
    rw [Nat.cast_pow, Int.toNat_of_nonneg heθhi0]
  case hq2 =>
    rw [Nat.cast_mul, Nat.cast_mul, Int.toNat_of_nonneg heθhi0,
      Int.toNat_of_nonneg heφhi0]
    push_cast
    ring
  case hq3 =>
    rw [Nat.cast_pow, Int.toNat_of_nonneg heφhi0]

