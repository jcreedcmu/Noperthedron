/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationDerivs
import Noperthedron.Bounding.OpNorm

/-!
# Symbolic algebra for rotation-derivative operators

The second- and third-partial developments work with operator-valued derivatives of
`rotR α ∘L rotM θ φ`. Through third order, every such operator is (up to sign) a
composition `head ∘L body` with `head ∈ {rotR, rotR'}` and `body` one of eight matrix
families. This file records that vocabulary as a tiny symbolic algebra:

* `Sign`, `Head`, `Body` — a sign, the head state, and the matrix-family state;
* `Term` — a signed composition, with `Term.eval` giving the actual operator;
* `Term.deriv` — symbolic coordinate differentiation (partial: transitions that would
  leave the vocabulary return `none`);
* `Head.deriv_correct`, `Body.derivθ_correct`, `Body.derivφ_correct` — each primitive
  transition is certified against the existing `HasDerivAt` lemmas;
* `secondTerm`/`thirdTerm` — the generated second- and third-order tables, with
  `second_defined`/`third_defined` showing all derivations through third order stay
  inside the vocabulary.

Structural consequences replace case-by-case reasoning: `Term.norm_le_one` bounds every
term uniformly, and the permutation symmetries `second_comm`, `third_swap_first`,
`third_swap_last` are decidable facts about the symbolic tables. `SecondPartialHelpers`
proves its hand-written `inner_second_partial_A`/`inner_third_partial_A` tables equal
the generated ones definitionally and inherits these properties.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

/-- Composition norm bound: ‖A ∘L B‖ ≤ 1 when ‖A‖ ≤ 1 and ‖B‖ ≤ 1 -/
lemma comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖A ∘L B‖ ≤ 1 :=
  calc ‖A ∘L B‖ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le A B
    _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Negated composition norm bound: ‖-(A ∘L B)‖ ≤ 1 when ‖A‖ ≤ 1 and ‖B‖ ≤ 1 -/
lemma neg_comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖-(A ∘L B)‖ ≤ 1 := by
  rw [norm_neg]; exact comp_norm_le_one hA hB

namespace SymbolicRotation

/-- A sign, acting on any type with negation. -/
inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

namespace Sign

def mul : Sign → Sign → Sign
  | .pos, s => s
  | .neg, .pos => .neg
  | .neg, .neg => .pos

def act {A : Type*} [Neg A] : Sign → A → A
  | .pos, a => a
  | .neg, a => -a

end Sign

/-- The head state of a rotation-derivative operator: `rotR` or `rotR'`. -/
inductive Head where
  | r
  | r'
  deriving DecidableEq, Repr

namespace Head

noncomputable def eval : Head → ℝ → (ℝ² →L[ℝ] ℝ²)
  | .r => rotR
  | .r' => rotR'

lemma norm_one (h : Head) (α : ℝ) : ‖h.eval α‖ = 1 := by
  cases h
  · exact Bounding.rotR_norm_one α
  · exact Bounding.rotR'_norm_one α

end Head

/-- The matrix-family state: the eight `rotM` derivative matrices needed through
third order. -/
inductive Body where
  | m
  | mθ
  | mφ
  | mθθ
  | mθφ
  | mφφ
  | mθθφ
  | mθφφ
  deriving DecidableEq, Repr

namespace Body

noncomputable def eval : Body → ℝ → ℝ → (ℝ³ →L[ℝ] ℝ²)
  | .m => rotM
  | .mθ => rotMθ
  | .mφ => rotMφ
  | .mθθ => rotMθθ
  | .mθφ => rotMθφ
  | .mφφ => rotMφφ
  | .mθθφ => rotMθθφ
  | .mθφφ => rotMθφφ

lemma norm_le_one (b : Body) (θ φ : ℝ) : ‖b.eval θ φ‖ ≤ 1 := by
  cases b
  · exact le_of_eq (Bounding.rotM_norm_one θ φ)
  · exact Bounding.rotMθ_norm_le_one θ φ
  · exact Bounding.rotMφ_norm_le_one θ φ
  · exact Bounding.rotMθθ_norm_le_one θ φ
  · exact Bounding.rotMθφ_norm_le_one θ φ
  · exact Bounding.rotMφφ_norm_le_one θ φ
  · exact Bounding.rotMθθφ_norm_le_one θ φ
  · exact Bounding.rotMθφφ_norm_le_one θ φ

end Body

/-- The three coordinate axes of the inner parameter space `(α, θ, φ)`. -/
inductive Axis where
  | α
  | θ
  | φ
  deriving DecidableEq, Repr

def axisOfFin : Fin 3 → Axis
  | 0 => .α
  | 1 => .θ
  | 2 => .φ

/-- A signed composition `± head ∘L body`. -/
structure Term where
  sign : Sign
  head : Head
  body : Body
  deriving DecidableEq, Repr

namespace Term

noncomputable def eval (t : Term) (α θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  t.sign.act (t.head.eval α ∘L t.body.eval θ φ)

/-- Every symbolic term denotes an operator of norm at most one. -/
lemma norm_le_one (t : Term) (α θ φ : ℝ) : ‖t.eval α θ φ‖ ≤ 1 := by
  rcases t with ⟨s, h, b⟩
  have hnorm := comp_norm_le_one (le_of_eq (h.norm_one α)) (b.norm_le_one θ φ)
  cases s <;> simpa [eval, Sign.act] using hnorm

def derivHead : Head → Sign × Head
  | .r => (.pos, .r')
  | .r' => (.neg, .r)

def derivBodyθ : Body → Option (Sign × Body)
  | .m => some (.pos, .mθ)
  | .mθ => some (.pos, .mθθ)
  | .mφ => some (.pos, .mθφ)
  | .mθθ => some (.neg, .mθ)
  | .mθφ => some (.pos, .mθθφ)
  | .mφφ => some (.pos, .mθφφ)
  | .mθθφ => none
  | .mθφφ => none

def derivBodyφ : Body → Option (Sign × Body)
  | .m => some (.pos, .mφ)
  | .mθ => some (.pos, .mθφ)
  | .mφ => some (.pos, .mφφ)
  | .mθθ => some (.pos, .mθθφ)
  | .mθφ => some (.pos, .mθφφ)
  | .mφφ => some (.neg, .mφ)
  | .mθθφ => none
  | .mθφφ => none

/-- Symbolic differentiation along a coordinate axis. `none` when the derivative
would leave the eight-state vocabulary (which cannot happen through third order,
see `second_defined`/`third_defined`). -/
def deriv (a : Axis) (t : Term) : Option Term :=
  match a with
  | .α =>
      let (s, h) := derivHead t.head
      some ⟨t.sign.mul s, h, t.body⟩
  | .θ => (derivBodyθ t.body).map fun (s, b) => ⟨t.sign.mul s, t.head, b⟩
  | .φ => (derivBodyφ t.body).map fun (s, b) => ⟨t.sign.mul s, t.head, b⟩

end Term

/-! ## Semantic checks for the primitive transitions -/

namespace Head

/-- The symbolic head transition agrees with the existing derivative theorems. -/
lemma deriv_correct (h : Head) (α : ℝ) (v : ℝ²) :
    let (s, h') := Term.derivHead h
    HasDerivAt (fun x => h.eval x v) (s.act (h'.eval α v)) α := by
  cases h
  · simpa [Term.derivHead, eval, Sign.act] using HasDerivAt_rotR α v
  · simpa [Term.derivHead, eval, Sign.act] using HasDerivAt_rotR' α v

end Head

namespace Body

/-- Every supported symbolic θ-transition agrees with the existing derivative theorems. -/
lemma derivθ_correct (b : Body) (θ φ : ℝ) (S : ℝ³) :
    match Term.derivBodyθ b with
    | none => True
    | some (s, b') =>
        HasDerivAt (fun x => b.eval x φ S) (s.act (b'.eval θ φ S)) θ := by
  cases b
  · simpa [Term.derivBodyθ, eval, Sign.act] using hasDerivAt_rotM_θ θ φ S
  · simpa [Term.derivBodyθ, eval, Sign.act] using hasDerivAt_rotMθ_θ θ φ S
  · simpa [Term.derivBodyθ, eval, Sign.act] using hasDerivAt_rotMφ_θ θ φ S
  · simpa [Term.derivBodyθ, eval, Sign.act] using hasDerivAt_rotMθθ_θ θ φ S
  · simpa [Term.derivBodyθ, eval, Sign.act] using hasDerivAt_rotMθφ_θ θ φ S
  · simpa [Term.derivBodyθ, eval, Sign.act] using hasDerivAt_rotMφφ_θ θ φ S
  · simp [Term.derivBodyθ]
  · simp [Term.derivBodyθ]

/-- Every supported symbolic φ-transition agrees with the existing derivative theorems. -/
lemma derivφ_correct (b : Body) (θ φ : ℝ) (S : ℝ³) :
    match Term.derivBodyφ b with
    | none => True
    | some (s, b') =>
        HasDerivAt (fun x => b.eval θ x S) (s.act (b'.eval θ φ S)) φ := by
  cases b
  · simpa [Term.derivBodyφ, eval, Sign.act] using hasDerivAt_rotM_φ θ φ S
  · simpa [Term.derivBodyφ, eval, Sign.act] using hasDerivAt_rotMθ_φ θ φ S
  · simpa [Term.derivBodyφ, eval, Sign.act] using hasDerivAt_rotMφ_φ θ φ S
  · simpa [Term.derivBodyφ, eval, Sign.act] using hasDerivAt_rotMθθ_φ θ φ S
  · simpa [Term.derivBodyφ, eval, Sign.act] using hasDerivAt_rotMθφ_φ θ φ S
  · simpa [Term.derivBodyφ, eval, Sign.act] using hasDerivAt_rotMφφ_φ θ φ S
  · simp [Term.derivBodyφ]
  · simp [Term.derivBodyφ]

end Body

/-! ## Iterated symbolic differentiation -/

/-- The base operator `rotR ∘L rotM`. -/
def baseTerm : Term := ⟨.pos, .r, .m⟩

/-- Apply the rightmost axis first, matching `nth_partial i (nth_partial j f)`. -/
def derive : List Axis → Term → Option Term
  | [], t => some t
  | a :: as, t => (derive as t).bind (Term.deriv a)

def derived (axes : List Axis) : Option Term := derive axes baseTerm

/-- The generated second-partial table. -/
def secondTerm (i j : Fin 3) : Term :=
  (derived [axisOfFin i, axisOfFin j]).getD baseTerm

/-- The generated third-partial table. -/
def thirdTerm (i j k : Fin 3) : Term :=
  (derived [axisOfFin i, axisOfFin j, axisOfFin k]).getD baseTerm

/-- The fallback in `secondTerm` is unreachable. -/
theorem second_defined (i j : Fin 3) :
    (derived [axisOfFin i, axisOfFin j]).isSome := by
  fin_cases i <;> fin_cases j <;> decide

/-- The fallback in `thirdTerm` is unreachable. -/
theorem third_defined (i j k : Fin 3) :
    (derived [axisOfFin i, axisOfFin j, axisOfFin k]).isSome := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-! ## Symbolic permutation symmetry -/

theorem second_comm (i j : Fin 3) : secondTerm i j = secondTerm j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem third_swap_first (i j k : Fin 3) : thirdTerm i j k = thirdTerm j i k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

theorem third_swap_last (i j k : Fin 3) : thirdTerm i j k = thirdTerm i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

end SymbolicRotation

end GlobalTheorem
