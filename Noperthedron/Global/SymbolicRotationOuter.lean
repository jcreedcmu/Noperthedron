/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.SymbolicRotationCore
import Noperthedron.Global.Basic

/-!
# Symbolic outer rotation derivatives

The outer projection depends only on the two angles `(θ, φ)`, and through third order
every operator in its partial-derivative tables is, up to sign, one of the eight `Body`
matrix families — there is no `rotR`/`rotR'` head. This file specializes the symbolic
machinery accordingly:

* `OuterTerm` — a signed body, with `OuterTerm.eval` giving the actual operator and
  `OuterTerm.norm_le_one` the uniform bound;
* `OuterTerm.deriv` — symbolic differentiation along the two outer axes, reusing the
  certified `Term.derivBodyθ`/`Term.derivBodyφ` transitions;
* `secondOuterTerm`/`thirdOuterTerm` — the generated outer tables, with definedness
  and permutation symmetries by `decide`;
* `OuterTerm.nth_partial_eval_eq` / `iterPartialOuter_eval_eq` — the semantic bridge on
  `E 2`, mirroring `Term.nth_partial_eval_eq` / `iterPartial_eval_eq`.

`SecondPartialOuter` instantiates these at `outerBase` to obtain its second- and
third-partial tables uniformly.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

namespace SymbolicRotation

/-- A signed body: outer rotation-derivative operators through third order are
`± body` with `body` one of the eight matrix families. -/
structure OuterTerm where
  sign : Sign
  body : Body
  deriving DecidableEq, Repr

namespace OuterTerm

noncomputable def eval (t : OuterTerm) (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  t.sign.act (t.body.eval θ φ)

/-- Every signed body denotes an operator of norm at most one. -/
lemma norm_le_one (t : OuterTerm) (θ φ : ℝ) : ‖t.eval θ φ‖ ≤ 1 := by
  rcases t with ⟨s, b⟩
  cases s <;> simpa [eval, Sign.act] using b.norm_le_one θ φ

/-- Symbolic differentiation along an outer axis (`0` = θ, `1` = φ), reusing the
certified body transitions. -/
def deriv (a : Fin 2) (t : OuterTerm) : Option OuterTerm :=
  match a with
  | 0 => (Term.derivBodyθ t.body).map fun (s, b) => ⟨t.sign.mul s, b⟩
  | 1 => (Term.derivBodyφ t.body).map fun (s, b) => ⟨t.sign.mul s, b⟩

end OuterTerm

/-- The base outer operator `rotM`. -/
def outerBase : OuterTerm := ⟨.pos, .m⟩

/-- Apply the rightmost axis first, matching `nth_partial i (nth_partial j f)`. -/
def deriveOuter : List (Fin 2) → OuterTerm → Option OuterTerm
  | [], t => some t
  | a :: as, t => (deriveOuter as t).bind (OuterTerm.deriv a)

def derivedOuter (axes : List (Fin 2)) : Option OuterTerm := deriveOuter axes outerBase

/-- The generated outer second-partial table. -/
def secondOuterTerm (i j : Fin 2) : OuterTerm := (derivedOuter [i, j]).getD outerBase

/-- The generated outer third-partial table. -/
def thirdOuterTerm (i j k : Fin 2) : OuterTerm := (derivedOuter [i, j, k]).getD outerBase

/-- The fallback in `secondOuterTerm` is unreachable. -/
theorem secondOuter_defined (i j : Fin 2) : (derivedOuter [i, j]).isSome := by
  fin_cases i <;> fin_cases j <;> decide

/-- The fallback in `thirdOuterTerm` is unreachable. -/
theorem thirdOuter_defined (i j k : Fin 2) : (derivedOuter [i, j, k]).isSome := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-! ## Symbolic permutation symmetry -/

theorem secondOuter_comm (i j : Fin 2) : secondOuterTerm i j = secondOuterTerm j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem thirdOuter_swap_first (i j k : Fin 2) :
    thirdOuterTerm i j k = thirdOuterTerm j i k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

theorem thirdOuter_swap_last (i j k : Fin 2) :
    thirdOuterTerm i j k = thirdOuterTerm i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-! ## Semantic bridge on `E 2` -/

namespace OuterTerm

/-- Pointwise evaluation of a signed body, unfolded. -/
lemma eval_apply (t : OuterTerm) (θ φ : ℝ) (S : ℝ³) :
    (t.eval θ φ) S = t.sign.act (t.body.eval θ φ S) := by
  rw [eval, Sign.act_apply]

/-- Every signed body evaluates to a map jointly differentiable in `(θ, φ)`. -/
lemma differentiable_eval_apply (t : OuterTerm) (S : ℝ³) :
    Differentiable ℝ fun z : E 2 => (t.eval (z.ofLp 0) (z.ofLp 1)) S := by
  have hb : Differentiable ℝ fun z : E 2 => t.body.eval (z.ofLp 0) (z.ofLp 1) S :=
    t.body.differentiable_comp (by fun_prop) (by fun_prop) (differentiable_const S)
  simp only [eval_apply]
  cases t.sign
  · simpa [Sign.act] using hb
  · simpa [Sign.act] using hb.neg

private lemma step_theta {t t' : OuterTerm} (hd : t.deriv 0 = some t') (S : ℝ³) (w : ℝ²) :
    nth_partial 0 (fun y : E 2 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫ := by
  simp only [deriv, Option.map_eq_some_iff] at hd
  obtain ⟨⟨s, b'⟩, hb, ht'⟩ := hd
  funext y
  show (fderiv ℝ _ y) (EuclideanSpace.single 0 1) = _
  rw [fderiv_inner_const _ w y _ (t.differentiable_eval_apply S y)]
  congr 1
  refine fderiv_single_eq (t.differentiable_eval_apply S y) ?_
  simp only [coord_single_same, coord_single_other (by decide : (1 : Fin 2) ≠ 0)]
  refine hasDerivAt_comp_add (fun x => (t.eval x (y.ofLp 1)) S) _ (y.ofLp 0) ?_
  simp only [eval_apply, ← ht', Sign.mul_act]
  exact t.sign.act_hasDerivAt (Body.derivθ_correct_of_eq hb (y.ofLp 0) (y.ofLp 1) S)

private lemma step_phi {t t' : OuterTerm} (hd : t.deriv 1 = some t') (S : ℝ³) (w : ℝ²) :
    nth_partial 1 (fun y : E 2 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫ := by
  simp only [deriv, Option.map_eq_some_iff] at hd
  obtain ⟨⟨s, b'⟩, hb, ht'⟩ := hd
  funext y
  show (fderiv ℝ _ y) (EuclideanSpace.single 1 1) = _
  rw [fderiv_inner_const _ w y _ (t.differentiable_eval_apply S y)]
  congr 1
  refine fderiv_single_eq (t.differentiable_eval_apply S y) ?_
  simp only [coord_single_same, coord_single_other (by decide : (0 : Fin 2) ≠ 1)]
  refine hasDerivAt_comp_add (fun x => (t.eval (y.ofLp 0) x) S) _ (y.ofLp 1) ?_
  simp only [eval_apply, ← ht', Sign.mul_act]
  exact t.sign.act_hasDerivAt (Body.derivφ_correct_of_eq hb (y.ofLp 0) (y.ofLp 1) S)

/-- **Semantic correctness of one outer symbolic differentiation step.** -/
lemma nth_partial_eval_eq {t t' : OuterTerm} (i : Fin 2)
    (hd : t.deriv i = some t') (S : ℝ³) (w : ℝ²) :
    nth_partial i (fun y : E 2 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫ := by
  fin_cases i
  · exact step_theta hd S w
  · exact step_phi hd S w

end OuterTerm

/-- Iterated outer coordinate partials, leftmost applied last (matching `deriveOuter`). -/
noncomputable def iterPartialOuter : List (Fin 2) → (E 2 → ℝ) → (E 2 → ℝ)
  | [], f => f
  | i :: is, f => nth_partial i (iterPartialOuter is f)

/-- **Iterated outer semantic correctness**: any defined outer symbolic derivation
computes the corresponding iterated partial derivative. -/
lemma iterPartialOuter_eval_eq (is : List (Fin 2)) {t t' : OuterTerm}
    (h : deriveOuter is t = some t') (S : ℝ³) (w : ℝ²) :
    iterPartialOuter is (fun y : E 2 => ⟪(t.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫) =
      fun y => ⟪(t'.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫ := by
  induction is generalizing t' with
  | nil =>
      simp only [deriveOuter, Option.some.injEq] at h
      rw [← h]
      rfl
  | cons i is ih =>
      simp only [deriveOuter, Option.bind_eq_some_iff] at h
      obtain ⟨t'', h1, h2⟩ := h
      show nth_partial i (iterPartialOuter is _) = _
      rw [ih h1, OuterTerm.nth_partial_eval_eq i h2 S w]

end SymbolicRotation

end GlobalTheorem
