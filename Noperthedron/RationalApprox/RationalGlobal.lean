import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Set.Operations
import Noperthedron.Global
import Noperthedron.PointSym
import Noperthedron.PoseInterval
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.BoundsKappa

open scoped RealInnerProductSpace

namespace RationalApprox.GlobalTheorem

/--
A measure of how far an inner-shadow vertex S can "stick out".

Second-order rational certificate: mirrors `GlobalTheorem.G` and adds the
κ-slack `4κ(1 + 3ε + (9/2)ε²)` — 4κ for the base term, 4κ per first-order
chain (weight ε each), and 4κ per second-order chain (total table weight 9,
each scaled by ε²/2).
-/
def Gℚ (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) : ℚ :=
  p.innerℚ S ⬝ᵥ w -
   (ε * (|p.rotR'ℚ (p.rotM₁ℚ S) ⬝ᵥ w| + |p.rotRℚ (p.rotM₁θℚ S) ⬝ᵥ w| + |p.rotRℚ (p.rotM₁φℚ S) ⬝ᵥ w|)
     + ε^2 / 2 * (|p.innerℚ S ⬝ᵥ w|
         + 2 * |p.rotR'ℚ (p.rotM₁θℚ S) ⬝ᵥ w| + 2 * |p.rotR'ℚ (p.rotM₁φℚ S) ⬝ᵥ w|
         + |p.rotRℚ (p.rotM₁θθℚ S) ⬝ᵥ w| + 2 * |p.rotRℚ (p.rotM₁θφℚ S) ⬝ᵥ w|
         + |p.rotRℚ (p.rotM₁φφℚ S) ⬝ᵥ w|)
     + 9 * ε^3 / 2 + 4 * κℚ * (1 + 3 * ε + 9/2 * ε^2))

/--
A measure of how far an outer-shadow vertex P can "reach" along w.

Second-order rational certificate; κ-slack `3κ(1 + 2ε + 2ε²)` (table weight 4
at scale ε²/2).
-/
def Hℚ (p : Pose ℚ) (ε : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) : ℚ :=
  p.rotM₂ℚ P ⬝ᵥ w + ε * (|p.rotM₂θℚ P ⬝ᵥ w| + |p.rotM₂φℚ P ⬝ᵥ w|)
    + ε^2 / 2 * (|p.rotM₂θθℚ P ⬝ᵥ w| + 2 * |p.rotM₂θφℚ P ⬝ᵥ w| + |p.rotM₂φφℚ P ⬝ᵥ w|)
    + 4 * ε^3 / 3 + 3 * κℚ * (1 + 2 * ε + 2 * ε^2)

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
def maxHℚ {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (ε : ℚ) (w : Fin 2 → ℚ) : ℚ :=
  Finset.image (Hℚ p ε w ∘ poly.v) Finset.univ  |>.max' <| by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr ne

/-! ### Fast `Gℚ > maxHℚ` check via per-pose hoisting -/

namespace Gℚ_gt_maxHℚ

/-- Pre-transposed `Mᵀ·w` 3-vectors so that each per-`P` `Hℚ` evaluation is just
three small dot products instead of three matrix-vector multiplies. -/
private structure HEntries : Type where
  m2tw   : Fin 3 → ℚ
  m2θtw  : Fin 3 → ℚ
  m2φtw  : Fin 3 → ℚ
  m2θθtw : Fin 3 → ℚ
  m2θφtw : Fin 3 → ℚ
  m2φφtw : Fin 3 → ℚ

@[inline] private def hEntries (p : Pose ℚ) (w : Fin 2 → ℚ) : HEntries :=
  let st := RationalApprox.sinℚ p.θ₂
  let ct := RationalApprox.cosℚ p.θ₂
  let sp := RationalApprox.sinℚ p.φ₂
  let cp := RationalApprox.cosℚ p.φ₂
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

private lemma m2θθtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θθtw ⬝ᵥ P = p.rotM₂θθℚ P ⬝ᵥ w := by
  unfold Pose.rotM₂θθℚ RationalApprox.rotMθθℚ RationalApprox.rotMθθℚ_mat
  rw [Matrix.toLin'_apply]
  simp [hEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m2θφtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θφtw ⬝ᵥ P = p.rotM₂θφℚ P ⬝ᵥ w := by
  unfold Pose.rotM₂θφℚ RationalApprox.rotMθφℚ RationalApprox.rotMθφℚ_mat
  rw [Matrix.toLin'_apply]
  simp [hEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m2φφtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2φφtw ⬝ᵥ P = p.rotM₂φφℚ P ⬝ᵥ w := by
  unfold Pose.rotM₂φφℚ RationalApprox.rotMφφℚ RationalApprox.rotMφφℚ_mat
  rw [Matrix.toLin'_apply]
  simp [hEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

@[inline] private def fastH (entries : HEntries) (ε : ℚ) (kappaTerm : ℚ) (P : Fin 3 → ℚ) : ℚ :=
  entries.m2tw ⬝ᵥ P + ε * (|entries.m2θtw ⬝ᵥ P| + |entries.m2φtw ⬝ᵥ P|)
    + ε^2 / 2 * (|entries.m2θθtw ⬝ᵥ P| + 2 * |entries.m2θφtw ⬝ᵥ P| + |entries.m2φφtw ⬝ᵥ P|)
    + 4 * ε^3 / 3 + kappaTerm

private lemma fastH_eq (p : Pose ℚ) (ε : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    fastH (hEntries p w) ε (3 * κℚ * (1 + 2 * ε + 2 * ε^2)) P = Hℚ p ε w P := by
  unfold fastH Hℚ
  rw [m2tw_dot_eq, m2θtw_dot_eq, m2φtw_dot_eq, m2θθtw_dot_eq, m2θφtw_dot_eq, m2φφtw_dot_eq]

/-- Pre-computed `(M_combined)ᵀ·w` 3-vectors for the four matrix chains in
`Gℚ` (`R·M₁`, `R'·M₁`, `R·M₁θ`, `R·M₁φ`). With these, each chain in `Gℚ`
collapses to a single 3-element dot product against `S`. -/
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

private lemma m1θR'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θR'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁θℚ S) ⬝ᵥ w := by
  unfold Pose.rotR'ℚ Pose.rotM₁θℚ RationalApprox.rotR'ℚ RationalApprox.rotMθℚ
        RationalApprox.rotR'ℚ_mat RationalApprox.rotMθℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m1φR'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φR'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁φℚ S) ⬝ᵥ w := by
  unfold Pose.rotR'ℚ Pose.rotM₁φℚ RationalApprox.rotR'ℚ RationalApprox.rotMφℚ
        RationalApprox.rotR'ℚ_mat RationalApprox.rotMφℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m1θθRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θθRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θθℚ S) ⬝ᵥ w := by
  unfold Pose.rotRℚ Pose.rotM₁θθℚ RationalApprox.rotRℚ RationalApprox.rotMθθℚ
        RationalApprox.rotRℚ_mat RationalApprox.rotMθθℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m1θφRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θφRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θφℚ S) ⬝ᵥ w := by
  unfold Pose.rotRℚ Pose.rotM₁θφℚ RationalApprox.rotRℚ RationalApprox.rotMθφℚ
        RationalApprox.rotRℚ_mat RationalApprox.rotMθφℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma m1φφRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φφRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁φφℚ S) ⬝ᵥ w := by
  unfold Pose.rotRℚ Pose.rotM₁φφℚ RationalApprox.rotRℚ RationalApprox.rotMφφℚ
        RationalApprox.rotRℚ_mat RationalApprox.rotMφφℚ_mat
  simp [gEntries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

@[inline] private def fastG (entries : GEntries) (ε : ℚ) (S : Fin 3 → ℚ) : ℚ :=
  let d := entries.m1RTw ⬝ᵥ S
  d - (ε * (|entries.m1R'Tw ⬝ᵥ S| + |entries.m1θRTw ⬝ᵥ S| + |entries.m1φRTw ⬝ᵥ S|)
     + ε^2 / 2 * (|d| + 2 * |entries.m1θR'Tw ⬝ᵥ S| + 2 * |entries.m1φR'Tw ⬝ᵥ S|
         + |entries.m1θθRTw ⬝ᵥ S| + 2 * |entries.m1θφRTw ⬝ᵥ S| + |entries.m1φφRTw ⬝ᵥ S|)
     + 9 * ε^3 / 2 + 4 * κℚ * (1 + 3 * ε + 9/2 * ε^2))

private lemma fastG_eq (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    fastG (gEntries p w) ε S = Gℚ p ε S w := by
  unfold fastG Gℚ
  rw [m1RTw_dot_eq, m1R'Tw_dot_eq, m1θRTw_dot_eq, m1φRTw_dot_eq,
    m1θR'Tw_dot_eq, m1φR'Tw_dot_eq, m1θθRTw_dot_eq, m1θφRTw_dot_eq, m1φφRTw_dot_eq]

end Gℚ_gt_maxHℚ

open Gℚ_gt_maxHℚ in
/-- Bool-valued `Gℚ > maxHℚ` check that hoists the trig partial sums and
the `Mᵀ·w` 3-vectors to per-pose work for both `Gℚ` and `Hℚ`; the
`∀ P ∈ poly.v` loop then only does small-value dot products. -/
def Gℚ_gt_maxHℚ_check {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ)
    (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) : Bool :=
  let hentries := hEntries p w
  let gentries := gEntries p w
  let g := fastG gentries ε S
  let kappaTerm := 3 * κℚ * (1 + 2 * ε + 2 * ε^2)
  decide <| ∀ k : ι, g > fastH hentries ε kappaTerm (poly.v k)

theorem Gℚ_gt_maxHℚ_check_iff {ι : Type} [Fintype ι] [DecidableEq ι] [ne : Nonempty ι]
    (p : Pose ℚ) (ε : ℚ) (S : Fin 3 → ℚ)
    (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ_check p ε S poly w = true ↔
      Gℚ p ε S w > maxHℚ p poly ε w := by
  unfold Gℚ_gt_maxHℚ_check maxHℚ
  simp only [decide_eq_true_eq]
  rw [Gℚ_gt_maxHℚ.fastG_eq]
  constructor
  · intro hAll
    show (Finset.image (Hℚ p ε w ∘ poly.v) Finset.univ).max' _ < Gℚ p ε S w
    rw [Finset.max'_lt_iff]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have := hAll k
    rw [Gℚ_gt_maxHℚ.fastH_eq] at this
    exact this
  · intro hLt k
    rw [Gℚ_gt_maxHℚ.fastH_eq]
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

private lemma Gℚ_le_G {p_ : Pose ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    {S : ℝ³} {S_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hS : ‖S‖ ≤ 1) (hS_approx : ‖S - toR3 S_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains p_) :
    Gℚ p_ ε S_ w ≤ GlobalTheorem.G p_.toReal ε S (toR2 w) := by
  set pbar := p_.toReal with hpbar
  unfold Gℚ GlobalTheorem.G
  rw [show pbar.inner S = pbar.rotR (pbar.rotM₁ S) by rw [Pose.inner_eq_RM]; rfl,
      show p_.innerℚ S_ = rotRℚ p_.α (rotMℚ p_.θ₁ p_.φ₁ S_) by rfl]
  show ⟪rotR (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
        ((ε : ℝ) * (|⟪rotR' (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    |⟪rotR (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    |⟪rotR (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫|) +
         (ε : ℝ)^2 / 2 * (|⟪rotR (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    2 * |⟪rotR' (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    2 * |⟪rotR' (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    |⟪rotR (p_.α : ℝ) (rotMθθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    2 * |⟪rotR (p_.α : ℝ) (rotMθφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
                    |⟪rotR (p_.α : ℝ) (rotMφφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫|) +
         9 * (ε : ℝ)^3 / 2) ≥ _
  have h_RM := bounds_kappa_RM
                (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
                hS hS_approx hw
  have h_R'M : ‖⟪rotR' (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotR'ℚ p_.α (rotMℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_R'M
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_RMθ : ‖⟪rotR (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotRℚ p_.α (rotMθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_RMθ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_RMφ : ‖⟪rotR (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotRℚ p_.α (rotMφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_RMφ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_R'Mθ : ‖⟪rotR' (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotR'ℚ p_.α (rotMθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_R'Mθ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_R'Mφ : ‖⟪rotR' (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotR'ℚ p_.α (rotMφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_R'Mφ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_RMθθ : ‖⟪rotR (p_.α : ℝ) (rotMθθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotRℚ p_.α (rotMθθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_RMθθ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_RMθφ : ‖⟪rotR (p_.α : ℝ) (rotMθφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotRℚ p_.α (rotMθφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_RMθφ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have h_RMφφ : ‖⟪rotR (p_.α : ℝ) (rotMφφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ -
                  ((rotRℚ p_.α (rotMφφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)‖ ≤ 4 * κ :=
    bounds_kappa_RMφφ
      (α := ⟨p_.α, hp.αBound⟩) (θ := ⟨p_.θ₁, hp.θ₁Bound⟩) (φ := ⟨p_.φ₁, hp.φ₁Bound⟩)
      hS hS_approx hw
  have hi_le : ((rotRℚ p_.α (rotMℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ) ≤
               ⟪rotR (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫ + 4 * κ := by
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
  have hε_real : (0 : ℝ) ≤ ε := mod_cast hε
  show _ ≤ _
  push_cast
  rw [h_κ]
  show _ -
        ((ε : ℝ) * (|((rotR'ℚ p_.α (rotMℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
                    |((rotRℚ p_.α (rotMθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
                    |((rotRℚ p_.α (rotMφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)|) +
         ((ε : ℝ))^2 / 2 * (|((rotRℚ p_.α (rotMℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
                    2 * |((rotR'ℚ p_.α (rotMθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
                    2 * |((rotR'ℚ p_.α (rotMφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
                    |((rotRℚ p_.α (rotMθθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
                    2 * |((rotRℚ p_.α (rotMθφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
                    |((rotRℚ p_.α (rotMφφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)|) +
         9 * ((ε : ℝ))^3 / 2 + 4 * κ * (1 + 3 * ((ε : ℝ)) + 9/2 * ((ε : ℝ))^2)) ≤ _
  have hfo : (ε : ℝ) * (|⟪rotR' (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
        |⟪rotR (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
        |⟪rotR (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫|)
      ≤ (ε : ℝ) * (|((rotR'ℚ p_.α (rotMℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
        |((rotRℚ p_.α (rotMθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
        |((rotRℚ p_.α (rotMφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| + 12 * κ) :=
    mul_le_mul_of_nonneg_left (by linarith [hR'_abs, hRθ_abs, hRφ_abs]) hε_real
  have hso : (ε : ℝ)^2 / 2 * (|⟪rotR (p_.α : ℝ) (rotM (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
        2 * |⟪rotR' (p_.α : ℝ) (rotMθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
        2 * |⟪rotR' (p_.α : ℝ) (rotMφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
        |⟪rotR (p_.α : ℝ) (rotMθθ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
        2 * |⟪rotR (p_.α : ℝ) (rotMθφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫| +
        |⟪rotR (p_.α : ℝ) (rotMφφ (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) S), toR2 w⟫|)
      ≤ (ε : ℝ)^2 / 2 * (|((rotRℚ p_.α (rotMℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
        2 * |((rotR'ℚ p_.α (rotMθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
        2 * |((rotR'ℚ p_.α (rotMφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
        |((rotRℚ p_.α (rotMθθℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
        2 * |((rotRℚ p_.α (rotMθφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| +
        |((rotRℚ p_.α (rotMφφℚ p_.θ₁ p_.φ₁ S_) ⬝ᵥ w : ℚ) : ℝ)| + 36 * κ) :=
    mul_le_mul_of_nonneg_left
      (by linarith [hRM_abs, hR'θ_abs, hR'φ_abs, hθθ_abs, hθφ_abs, hφφ_abs])
      (by positivity)
  linarith [hi_le, hfo, hso]

private lemma H_le_Hℚ {pbar : Pose ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    {P : ℝ³} {P_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains pbar) :
    GlobalTheorem.H pbar.toReal ε (toR2 w) P ≤ Hℚ pbar ε w P_ := by
  unfold GlobalTheorem.H Hℚ Pose.rotM₂ Pose.rotM₂θ Pose.rotM₂φ
        Pose.rotM₂θθ Pose.rotM₂θφ Pose.rotM₂φφ
        Pose.rotM₂ℚ Pose.rotM₂θℚ Pose.rotM₂φℚ
        Pose.rotM₂θθℚ Pose.rotM₂θφℚ Pose.rotM₂φφℚ
  show ⟪rotM (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫ +
        (ε : ℝ) * (|⟪rotMθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| +
                   |⟪rotMφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫|) +
        (ε : ℝ)^2 / 2 * (|⟪rotMθθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| +
                   2 * |⟪rotMθφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| +
                   |⟪rotMφφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫|) +
        4 * (ε : ℝ)^3 / 3 ≤ _
  have h_M := bounds_kappa_M
                (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩)
                hP hP_approx hw
  have h_Mθ := bounds_kappa_Mθ
                (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩)
                hP hP_approx hw
  have h_Mφ := bounds_kappa_Mφ
                (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩)
                hP hP_approx hw
  have h_Mθθ := bounds_kappa_Mθθ
                (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩)
                hP hP_approx hw
  have h_Mθφ := bounds_kappa_Mθφ
                (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩)
                hP hP_approx hw
  have h_Mφφ := bounds_kappa_Mφφ
                (θ := ⟨pbar.θ₂, hp.θ₂Bound⟩) (φ := ⟨pbar.φ₂, hp.φ₂Bound⟩)
                hP hP_approx hw
  have hm_le : ⟪rotM (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫ ≤
               ((rotMℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ) + 3 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_M; rw [abs_le] at this
    linarith [this.2]
  have hθ_abs : |⟪rotMθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| ≤
                |((rotMθℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| + 3 * κ :=
    abs_le_abs_add_of_norm_sub_le h_Mθ
  have hφ_abs : |⟪rotMφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| ≤
                |((rotMφℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| + 3 * κ :=
    abs_le_abs_add_of_norm_sub_le h_Mφ
  have hθθ_abs : |⟪rotMθθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| ≤
                |((rotMθθℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| + 3 * κ :=
    abs_le_abs_add_of_norm_sub_le h_Mθθ
  have hθφ_abs : |⟪rotMθφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| ≤
                |((rotMθφℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| + 3 * κ :=
    abs_le_abs_add_of_norm_sub_le h_Mθφ
  have hφφ_abs : |⟪rotMφφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| ≤
                |((rotMφφℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| + 3 * κ :=
    abs_le_abs_add_of_norm_sub_le h_Mφφ
  have h_κ : ((κℚ : ℚ) : ℝ) = κ := cast_κℚ
  have hε_real : (0 : ℝ) ≤ ε := mod_cast hε
  push_cast
  rw [h_κ]
  have hfo : (ε : ℝ) * (|⟪rotMθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| +
        |⟪rotMφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫|)
      ≤ (ε : ℝ) * (|((rotMθℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| +
        |((rotMφℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| + 6 * κ) :=
    mul_le_mul_of_nonneg_left (by linarith [hθ_abs, hφ_abs]) hε_real
  have hso : (ε : ℝ)^2 / 2 * (|⟪rotMθθ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| +
        2 * |⟪rotMθφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫| +
        |⟪rotMφφ (pbar.θ₂ : ℝ) (pbar.φ₂ : ℝ) P, toR2 w⟫|)
      ≤ (ε : ℝ)^2 / 2 * (|((rotMθθℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| +
        2 * |((rotMθφℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| +
        |((rotMφφℚ pbar.θ₂ pbar.φ₂ P_ ⬝ᵥ w : ℚ) : ℝ)| + 12 * κ) :=
    mul_le_mul_of_nonneg_left (by linarith [hθθ_abs, hθφ_abs, hφφ_abs]) (by positivity)
  linarith [hm_le, hfo, hso]

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
    simpa [S_real, i, j, Polyhedron.toReal] using happrox.approx (happrox.bijection.symm j)
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
    have h_le_max : Hℚ p ε pc.w (poly_.v k') ≤ maxHℚ p poly_ ε pc.w :=
      Finset.le_max' _ ((Hℚ p ε pc.w ∘ poly_.v) k')
        (Finset.mem_image_of_mem _ (Finset.mem_univ k'))
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
