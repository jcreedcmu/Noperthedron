/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.SymbolicRotationCore
import Noperthedron.Global.Basic

/-!
# Semantic correctness for symbolic rotation derivatives

`SymbolicRotationDerivs` defines the symbolic algebra (`Sign`, `Head`, `Body`, `Term`,
`Term.deriv`, `derive`) and certifies each primitive transition against the existing
`HasDerivAt` lemmas. This file supplies the semantic bridge from the algebra to actual
partial derivatives:

* `Term.differentiable_eval_apply` — every term evaluates to a map jointly
  differentiable in `(α, θ, φ)`;
* `Term.nth_partial_eval_eq` — **one symbolic differentiation step is semantically
  correct**: if `t.deriv (axisOfFin i) = some t'`, then the `i`-th partial of
  `⟪t.eval … S, w⟫` is `⟪t'.eval … S, w⟫`;
* `iterPartial_eval_eq` — by induction, any defined symbolic derivation computes the
  corresponding iterated partial derivative.

Consumers instantiate these at `baseTerm` to obtain the first-, second-, and
third-partial formulas for `rotproj_inner` uniformly, replacing per-case `fderiv`
computations.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

namespace SymbolicRotation

/-! ### Extraction forms of the primitive correctness lemmas -/

/-- `Head.deriv_correct` with the transition given by its projections. -/
private lemma Head.deriv_correct' (h : Head) (α : ℝ) (v : ℝ²) :
    HasDerivAt (fun x => h.eval x v)
      ((Term.derivHead h).1.act ((Term.derivHead h).2.eval α v)) α := by
  cases h
  · simpa [Term.derivHead, Head.eval, Sign.act] using HasDerivAt_rotR α v
  · simpa [Term.derivHead, Head.eval, Sign.act] using HasDerivAt_rotR' α v

/-- Joint differentiability of every body family in the two angles and the vector. -/
lemma Body.differentiable_eval (b : Body) (S : ℝ³) :
    Differentiable ℝ fun z : E 3 => b.eval (z.ofLp 1) (z.ofLp 2) S :=
  b.differentiable_comp (by fun_prop) (by fun_prop) (differentiable_const S)

namespace Term

/-- Pointwise evaluation of a term, unfolded to head-applied-to-body form. -/
lemma eval_apply (t : Term) (α θ φ : ℝ) (S : ℝ³) :
    (t.eval α θ φ) S = t.sign.act (t.head.eval α (t.body.eval θ φ S)) := by
  rw [eval, Sign.act_apply]
  rfl

/-- Every term evaluates to a map jointly differentiable in `(α, θ, φ)`. -/
lemma differentiable_eval_apply (t : Term) (S : ℝ³) :
    Differentiable ℝ fun z : E 3 => (t.eval (z.ofLp 0) (z.ofLp 1) (z.ofLp 2)) S := by
  have hb := t.body.differentiable_eval S
  have hcomp : Differentiable ℝ
      fun z : E 3 => t.head.eval (z.ofLp 0) (t.body.eval (z.ofLp 1) (z.ofLp 2) S) := by
    cases t.head
    · exact differentiable_rotR_comp (by fun_prop) hb
    · exact differentiable_rotR'_comp (by fun_prop) hb
  simp only [eval_apply]
  cases t.sign
  · simpa [Sign.act] using hcomp
  · simpa [Sign.act] using hcomp.neg

/-! ### The generic step lemma, one private lemma per axis -/

private lemma step_alpha {t t' : Term} (hd : t.deriv .α = some t') (S : ℝ³) (w : ℝ²) :
    nth_partial 0 (fun y : E 3 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫ := by
  have ht' : t' = ⟨t.sign.mul (derivHead t.head).1, (derivHead t.head).2, t.body⟩ := by
    simp only [deriv] at hd
    exact (Option.some.inj hd).symm
  funext y
  show (fderiv ℝ _ y) (EuclideanSpace.single 0 1) = _
  rw [fderiv_inner_const _ w y _ (t.differentiable_eval_apply S y)]
  congr 1
  refine fderiv_single_eq (t.differentiable_eval_apply S y) ?_
  simp only [coord_e0_same, coord_e0_at1, coord_e0_at2]
  refine hasDerivAt_comp_add
    (fun x => (t.eval x (y.ofLp 1) (y.ofLp 2)) S) _ (y.ofLp 0) ?_
  simp only [eval_apply, ht', Sign.mul_act]
  exact t.sign.act_hasDerivAt (Head.deriv_correct' t.head (y.ofLp 0) _)

private lemma step_theta {t t' : Term} (hd : t.deriv .θ = some t') (S : ℝ³) (w : ℝ²) :
    nth_partial 1 (fun y : E 3 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫ := by
  simp only [deriv, Option.map_eq_some_iff] at hd
  obtain ⟨⟨s, b'⟩, hb, ht'⟩ := hd
  funext y
  show (fderiv ℝ _ y) (EuclideanSpace.single 1 1) = _
  rw [fderiv_inner_const _ w y _ (t.differentiable_eval_apply S y)]
  congr 1
  refine fderiv_single_eq (t.differentiable_eval_apply S y) ?_
  simp only [coord_e1_same, coord_e1_at0, coord_e1_at2]
  refine hasDerivAt_comp_add
    (fun x => (t.eval (y.ofLp 0) x (y.ofLp 2)) S) _ (y.ofLp 1) ?_
  simp only [eval_apply, ← ht', Sign.mul_act]
  have hcomp := (t.head.eval (y.ofLp 0)).hasFDerivAt.comp_hasDerivAt _
    (Body.derivθ_correct_of_eq hb (y.ofLp 1) (y.ofLp 2) S)
  rw [Sign.clm_act] at hcomp
  exact t.sign.act_hasDerivAt hcomp

private lemma step_phi {t t' : Term} (hd : t.deriv .φ = some t') (S : ℝ³) (w : ℝ²) :
    nth_partial 2 (fun y : E 3 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫ := by
  simp only [deriv, Option.map_eq_some_iff] at hd
  obtain ⟨⟨s, b'⟩, hb, ht'⟩ := hd
  funext y
  show (fderiv ℝ _ y) (EuclideanSpace.single 2 1) = _
  rw [fderiv_inner_const _ w y _ (t.differentiable_eval_apply S y)]
  congr 1
  refine fderiv_single_eq (t.differentiable_eval_apply S y) ?_
  simp only [coord_e2_same, coord_e2_at0, coord_e2_at1]
  refine hasDerivAt_comp_add
    (fun x => (t.eval (y.ofLp 0) (y.ofLp 1) x) S) _ (y.ofLp 2) ?_
  simp only [eval_apply, ← ht', Sign.mul_act]
  have hcomp := (t.head.eval (y.ofLp 0)).hasFDerivAt.comp_hasDerivAt _
    (Body.derivφ_correct_of_eq hb (y.ofLp 1) (y.ofLp 2) S)
  rw [Sign.clm_act] at hcomp
  exact t.sign.act_hasDerivAt hcomp

/-- **Semantic correctness of one symbolic differentiation step**: if the symbolic
derivative along axis `i` is defined, it computes the corresponding `nth_partial`. -/
lemma nth_partial_eval_eq {t t' : Term} (i : Fin 3)
    (hd : t.deriv (axisOfFin i) = some t') (S : ℝ³) (w : ℝ²) :
    nth_partial i (fun y : E 3 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫ := by
  fin_cases i
  · exact step_alpha hd S w
  · exact step_theta hd S w
  · exact step_phi hd S w

end Term

/-! ### Iterated form -/

/-- Iterated coordinate partials, leftmost applied last (matching `derive`). -/
noncomputable def iterPartial : List (Fin 3) → (E 3 → ℝ) → (E 3 → ℝ)
  | [], f => f
  | i :: is, f => nth_partial i (iterPartial is f)

/-- **Iterated semantic correctness**: any defined symbolic derivation computes the
corresponding iterated partial derivative. -/
lemma iterPartial_eval_eq (is : List (Fin 3)) {t t' : Term}
    (h : derive (is.map axisOfFin) t = some t') (S : ℝ³) (w : ℝ²) :
    iterPartial is (fun y : E 3 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫ := by
  induction is generalizing t' with
  | nil =>
      simp only [List.map_nil, derive, Option.some.injEq] at h
      rw [← h]
      rfl
  | cons i is ih =>
      simp only [List.map_cons, derive, Option.bind_eq_some_iff] at h
      obtain ⟨t'', h1, h2⟩ := h
      show nth_partial i (iterPartial is _) = _
      rw [ih h1, Term.nth_partial_eval_eq i h2 S w]

end SymbolicRotation

end GlobalTheorem
