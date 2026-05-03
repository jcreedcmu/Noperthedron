import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.DeriveFintype

import Noperthedron.PoseInterval
import Noperthedron.Vertices.Index
import Noperthedron.Vertices.Python

namespace Noperthedron.Solution

/-! ## Constants -/

def DENOMQ : ℚ := 15360000

inductive Param where | θ₁ | φ₁ | θ₂ | φ₂ | α
deriving BEq, ReflBEq, LawfulBEq, Repr, Fintype, DecidableEq, Nonempty

end Noperthedron.Solution

/-! ## `Param`-indexed access on `Pose` -/

namespace Pose
variable {R : Type}

/-- Read the component of a `Pose` selected by a `Solution.Param`. -/
def getParam (p : Pose R) : Noperthedron.Solution.Param → R
  | .θ₁ => p.θ₁
  | .θ₂ => p.θ₂
  | .φ₁ => p.φ₁
  | .φ₂ => p.φ₂
  | .α  => p.α

/-- Replace the component of a `Pose` selected by a `Solution.Param`. -/
def setParam (p : Pose R) : Noperthedron.Solution.Param → R → Pose R
  | .θ₁, x => { p with θ₁ := x }
  | .θ₂, x => { p with θ₂ := x }
  | .φ₁, x => { p with φ₁ := x }
  | .φ₂, x => { p with φ₂ := x }
  | .α,  x => { p with α  := x }

@[simp] lemma getParam_setParam_self (p : Pose R) (a : Noperthedron.Solution.Param) (x : R) :
    (p.setParam a x).getParam a = x := by cases a <;> rfl

@[simp] lemma getParam_setParam_of_ne (p : Pose R) {a b : Noperthedron.Solution.Param}
    (h : b ≠ a) (x : R) :
    (p.setParam a x).getParam b = p.getParam b := by
  cases a <;> cases b <;> first | rfl | (exact absurd rfl h)

lemma le_iff_forall_getParam [PartialOrder R] (p q : Pose R) :
    p ≤ q ↔ ∀ a : Noperthedron.Solution.Param, p.getParam a ≤ q.getParam a := by
  rw [le_iff]
  refine ⟨fun ⟨h1, h2, h3, h4, h5⟩ a => by cases a <;> assumption,
          fun h => ⟨h .θ₁, h .θ₂, h .φ₁, h .φ₂, h .α⟩⟩

end Pose

namespace Noperthedron.Solution

/-- A solution-table interval is a `PoseInterval ℚ`: a `min ≤ max` pair of rational
poses bounding a 5d box in parameter space. Stored values are the actual angle values
(post-DENOMQ division); the loader for the SY25 CSV is responsible for dividing the
raw integer numerators by `DENOMQ` when constructing the interval. -/
abbrev Interval : Type := PoseInterval ℚ

/--
A `Solution.Row` aims to closely model of exactly the data in Steininger and Yurkevich's big CSV file.
IDs start from zero. See [SY25] §7.1 for the meaning of all these fields.
-/
structure Row : Type where
   ID : ℕ
   nodeType : ℕ
   nrChildren : ℕ
   IDfirstChild : ℕ
   split : ℕ
   interval : Interval
   S_index : VertexIndex
   wx_numerator : ℤ
   wy_numerator : ℤ
   w_denominator : ℕ
   P1_index : VertexIndex
   P2_index : VertexIndex
   P3_index : VertexIndex
   Q1_index : VertexIndex
   Q2_index : VertexIndex
   Q3_index : VertexIndex
   r' : ℤ
   sigma_Q : Finset.Icc 0 1

instance : ToString Row where
  toString r := s!"\{ID := {r.ID}, nodeType := {r.nodeType}, nrChildren := {r.nrChildren}, ...}"

abbrev Table : Type := Array Row

def interpolate (min max : ℚ) (N : ℕ) [NeZero N] (n : ℕ) : ℝ :=
  AffineMap.lineMap min max ((n : ℚ) / N)

def Interval.interpolate (param : Param) (iv : Interval) (N : ℕ) [NeZero N] (n : ℕ) : ℚ :=
  AffineMap.lineMap (iv.min.getParam param) (iv.max.getParam param) ((n : ℚ) / N)

/--
The two endpoints constructed below by `Interval.nth_part` are correctly oriented.
-/
def interpolates_le (param : Param) (iv : Interval) (N : ℕ) [NeZero N] (n : ℕ) :
    iv.min.setParam param (iv.interpolate param N ↑n) ≤
    iv.max.setParam param (iv.interpolate param N (↑n + 1)) := by
  rw [Pose.le_iff_forall_getParam]
  intro b
  have h := (Pose.le_iff_forall_getParam iv.min iv.max).mp iv.fst_le_snd b
  rcases eq_or_ne b param with rfl | hne
  · simp [Interval.interpolate, AffineMap.lineMap]
    have : N ≠ 0 := Ne.symm (NeZero.ne' N)
    field_simp
    linarith
  · simpa [Pose.getParam_setParam_of_ne _ hne]

/--
Given an interval `iv`, and a parameter `param`, return the interval that results from
subdividing `iv` along `param` into `N` equal parts, and picking the `n`th one.
-/
def Interval.nth_part (param : Param) (iv : Interval) (N : ℕ) [hN : NeZero N] (n : Fin N) : Interval :=
    PoseInterval.mk
      (iv.min.setParam param (iv.interpolate param N n))
      (iv.max.setParam param (iv.interpolate param N (n+1)))
      (interpolates_le param iv N n)

def Interval.lower_half (param : Param) (iv : Interval) : Interval := Interval.nth_part param iv 2 0
def Interval.upper_half (param : Param) (iv : Interval) : Interval := Interval.nth_part param iv 2 1

/-- Build an `Interval` from `Pose ℤ` endpoints holding the raw `DENOMQ`-scaled
integer numerators (the form used in the SY25 CSV). The constructor divides each
component by `DENOMQ` so the resulting `Interval` carries actual angle values. -/
def Interval.ofIntPose (mn mx : Pose ℤ) (h : mn ≤ mx) : Interval :=
  PoseInterval.mk
    { θ₁ := (mn.θ₁ : ℚ) / DENOMQ, θ₂ := (mn.θ₂ : ℚ) / DENOMQ,
      φ₁ := (mn.φ₁ : ℚ) / DENOMQ, φ₂ := (mn.φ₂ : ℚ) / DENOMQ,
      α  := (mn.α  : ℚ) / DENOMQ }
    { θ₁ := (mx.θ₁ : ℚ) / DENOMQ, θ₂ := (mx.θ₂ : ℚ) / DENOMQ,
      φ₁ := (mx.φ₁ : ℚ) / DENOMQ, φ₂ := (mx.φ₂ : ℚ) / DENOMQ,
      α  := (mx.α  : ℚ) / DENOMQ }
    (by
      have hD : (0 : ℚ) ≤ DENOMQ := by norm_num [DENOMQ]
      obtain ⟨h1, h2, h3, h4, h5⟩ := (Pose.le_iff mn mx).mp h
      rw [Pose.le_iff]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        exact div_le_div_of_nonneg_right (by exact_mod_cast ‹_›) hD)

/-- Center of an interval box along one parameter, as a rational. -/
def Interval.center (iv : Interval) (p : Param) : ℚ :=
  (iv.min.getParam p + iv.max.getParam p) / 2

/-- Center of an interval box, as a `Pose ℚ`. -/
def Interval.centerPose (iv : Interval) : Pose ℚ where
  θ₁ := iv.center .θ₁
  θ₂ := iv.center .θ₂
  φ₁ := iv.center .φ₁
  φ₂ := iv.center .φ₂
  α  := iv.center .α

abbrev Row.θ₁ (r : Row) : ℚ := r.interval.center .θ₁
abbrev Row.φ₁ (r : Row) : ℚ := r.interval.center .φ₁
abbrev Row.θ₂ (r : Row) : ℚ := r.interval.center .θ₂
abbrev Row.φ₂ (r : Row) : ℚ := r.interval.center .φ₂
abbrev Row.α (r : Row) : ℚ := r.interval.center .α

/-- Max half-width of the row's interval box across all 5 parameters. -/
abbrev Row.epsilon (r : Row) : ℚ := r.interval.radius

abbrev Row.S (r : Row) : Fin 3 → ℚ := pythonVertex r.S_index

abbrev Row.w (r : Row) :  Fin 2 → ℚ
| 0 => r.wx_numerator / r.w_denominator
| 1 => r.wy_numerator / r.w_denominator

/--
`cubeFold fs b as`, takes a list of functions `fs` and a starting value `b` and a list of
coordinates `as` and returns a list of length `|fs|^|as|` consisting of all the ways
of folding the initial value `b` through some sequence of functions in `fs`, using values from `as`.
-/
def cubeFold {α β : Type} (fs : List (α → β → β)) (b : β) : List α → List β
| [] => [b]
| (h :: tl) => fs.flatMap (fun f => cubeFold fs (f h b) tl)

/-
Equivalently I probably could have done

def cubeFold {α β : Type} (fs : List (α → β → β)) (b : β) : List α → List β
| [] => pure b
| (h :: tl) => do  cubeFold fs ((← fs) h b) tl

but I imagine it might be less annoying to do reasoning on the expanded-out nonmonadic version.
-/
section Test

def example_interval : Interval :=
  PoseInterval.mk
    { θ₁ := 100, θ₂ := 200, φ₁ := 300, φ₂ := 400, α := 16 }
    { θ₁ := 116, θ₂ := 216, φ₁ := 316, φ₂ := 416, α := 32 }
    (by decide)

/--
info: [({ θ₁ := 100, θ₂ := 200, φ₁ := 300, φ₂ := 400, α := 16 }, { θ₁ := 108, θ₂ := 208, φ₁ := 316, φ₂ := 416, α := 32 }),
 ({ θ₁ := 100, θ₂ := 208, φ₁ := 300, φ₂ := 400, α := 16 }, { θ₁ := 108, θ₂ := 216, φ₁ := 316, φ₂ := 416, α := 32 }),
 ({ θ₁ := 108, θ₂ := 200, φ₁ := 300, φ₂ := 400, α := 16 }, { θ₁ := 116, θ₂ := 208, φ₁ := 316, φ₂ := 416, α := 32 }),
 ({ θ₁ := 108, θ₂ := 208, φ₁ := 300, φ₂ := 400, α := 16 }, { θ₁ := 116, θ₂ := 216, φ₁ := 316, φ₂ := 416, α := 32 })]
-/
#guard_msgs in
#eval (cubeFold (α := Param) (β := Interval)
        [Interval.lower_half, Interval.upper_half] example_interval [.θ₁, .θ₂]).map
      (·.toProd)

end Test
