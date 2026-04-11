import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.DeriveFintype

namespace Noperthedron.Solution

inductive Param where | θ₁ | φ₁ | θ₂ | φ₂ | α
deriving BEq, ReflBEq, LawfulBEq, Repr, Fintype, DecidableEq

structure Interval where
  min : Param → ℤ
  max : Param → ℤ
deriving DecidableEq

instance : Repr Interval where
  reprPrec i _ :=
    let params := [Param.θ₁, Param.φ₁, Param.θ₂, Param.φ₂, Param.α]
    let entries := params.map fun p =>
      s!"{repr p}: [{i.min p}, {i.max p}]"
    "{" ++ String.intercalate ",\n" entries ++ "}"

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
   S_index : Fin 90
   wx_numerator : ℤ
   wy_numerator : ℤ
   w_denominator : ℕ
   P1_index : ℕ
   P2_index : ℕ
   P3_index : ℕ
   Q1_index : ℕ
   Q2_index : ℕ
   Q3_index : ℕ
   r : ℤ
   sigma_Q : Finset.Icc 0 1

abbrev Table : Type := Array Row

def Interval.lower_half (param : Param) (interval : Interval) : Interval := {
  min := interval.min
  max := Function.update interval.max param ((interval.min param + interval.max param)/2)
}

def Interval.upper_half (param : Param) (interval : Interval) : Interval := {
  min := Function.update interval.min param ((interval.min param + interval.max param)/2)
  max := interval.max
}

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

def example_interval : Interval := {
  min := fun
  | .θ₁ => 100
  | .θ₂ => 200
  | .φ₁ => 300
  | .φ₂ => 400
  | .α => 16
  max := fun
  | .θ₁ => 116
  | .θ₂ => 216
  | .φ₁ => 316
  | .φ₂ => 416
  | .α => 32
}

/--
info: [{Noperthedron.Solution.Param.θ₁: [100, 108],
 Noperthedron.Solution.Param.φ₁: [300, 316],
 Noperthedron.Solution.Param.θ₂: [200, 208],
 Noperthedron.Solution.Param.φ₂: [400, 416],
 Noperthedron.Solution.Param.α: [16, 32]},
 {Noperthedron.Solution.Param.θ₁: [100, 108],
 Noperthedron.Solution.Param.φ₁: [300, 316],
 Noperthedron.Solution.Param.θ₂: [208, 216],
 Noperthedron.Solution.Param.φ₂: [400, 416],
 Noperthedron.Solution.Param.α: [16, 32]},
 {Noperthedron.Solution.Param.θ₁: [108, 116],
 Noperthedron.Solution.Param.φ₁: [300, 316],
 Noperthedron.Solution.Param.θ₂: [200, 208],
 Noperthedron.Solution.Param.φ₂: [400, 416],
 Noperthedron.Solution.Param.α: [16, 32]},
 {Noperthedron.Solution.Param.θ₁: [108, 116],
 Noperthedron.Solution.Param.φ₁: [300, 316],
 Noperthedron.Solution.Param.θ₂: [208, 216],
 Noperthedron.Solution.Param.φ₂: [400, 416],
 Noperthedron.Solution.Param.α: [16, 32]}]
-/
#guard_msgs in
#eval cubeFold (α := Param) (β := Interval) [Interval.lower_half, Interval.upper_half] example_interval [.θ₁, .θ₂]

end Test
