import Mathlib.Data.Real.Basic
import Noperthedron.PoseInterval

namespace Solution

inductive Param where | θ₁ | φ₁ | θ₂ | φ₂ | α
deriving BEq, Repr

structure Interval where
  min : Param → ℕ
  max : Param → ℕ

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
   A_max : ℤ
   A_min : ℤ
   S_index : Fin 30
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

/-
Do we want to write this validity checker instead as a manifestly
computational program returning Bool?
-/

def Row.ValidGlobal (tab : Table) (row : Row) : Prop :=
  row.nodeType = 1 ∧ sorry

def Row.ValidLocal (tab : Table) (row : Row) : Prop :=
  row.nodeType = 2 ∧ sorry

def Interval.lower_half (param : Param) (interval : Interval) : Interval := {
  min := interval.min
  max := fun p => if p == param then (interval.min p + interval.max p)/2 else interval.max p
}

def Interval.upper_half (param : Param) (interval : Interval) : Interval := {
  min := fun p => if p == param then (interval.min p + interval.max p)/2 else interval.min p
  max := interval.max
}

structure Row.ValidSplitParam (tab : Table) (row : Row) (param : Param) : Prop where
  split : row.split = 1
  bound1 : row.IDfirstChild < Array.size tab
  bound2 : row.IDfirstChild + 1< Array.size tab
  first_child_good : tab[row.IDfirstChild].interval = row.interval.lower_half param
  second_child_good : tab[row.IDfirstChild + 1].interval = row.interval.upper_half param

def Row.ValidBinarySplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 2 ∧
    ((row.split = 1 ∧ row.ValidSplitParam tab .θ₁) ∨
     (row.split = 2 ∧ row.ValidSplitParam tab .φ₁) ∨
     (row.split = 3 ∧ row.ValidSplitParam tab .θ₂) ∨
     (row.split = 4 ∧ row.ValidSplitParam tab .φ₂) ∨
     (row.split = 5 ∧ row.ValidSplitParam tab .α))

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
info: [{Solution.Param.θ₁: [100, 108],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [200, 208],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]},
 {Solution.Param.θ₁: [100, 108],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [208, 216],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]},
 {Solution.Param.θ₁: [108, 116],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [200, 208],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]},
 {Solution.Param.θ₁: [108, 116],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [208, 216],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]}]
-/
#guard_msgs in
#eval cubeFold (α := Param) (β := Interval) [Interval.lower_half, Interval.upper_half] example_interval [.θ₁, .θ₂]

end Test

def Table.HasIntervals (tab : Table) (start : ℕ) (intervals : List Interval) : Prop :=
  ∀ i : Fin intervals.length,
    ∃ (h : start + i.val < tab.size), tab[start + i.val].interval = intervals[i]

def Row.ValidFullSplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 32 ∧ row.split = 6 ∧
  tab.HasIntervals row.IDfirstChild (cubeFold [Interval.lower_half, Interval.upper_half] row.interval [.θ₁, .φ₁, .θ₂, .φ₂, .α])

def Row.ValidSplit (tab : Table) (row : Row) : Prop :=
  (row.nodeType = (3 : ℕ)) ∧ row.ValidBinarySplit tab ∨ row.ValidFullSplit tab

inductive Row.Valid (tab : Table) (row : Row) : Prop where
  | asSplit : row.ValidSplit tab → Row.Valid tab row
  | asGlobal : row.ValidGlobal tab → Row.Valid tab row
  | asLocal : row.ValidLocal tab → Row.Valid tab row

def Table.Valid (tab : Table) : Prop :=
  ∀ i : Fin (tab.size), let row := tab[i]; row.ID = i ∧ row.Valid tab

def Table.valid_decidable (tab : Table) : Decidable tab.Valid := by
  sorry

/--
The common denominator of θ₁, θ₂, φ₁, φ₂, α rational
representations in the table. See [SY25 §7.2]
-/
def N : ℕ := 15360000

noncomputable
def Row.toPoseInterval (row : Row) : PoseInterval where
  min := { θ₁ := row.interval.min .θ₁ / N
           θ₂ := row.interval.min .θ₂ / N
           φ₁ := row.interval.min .φ₁ / N
           φ₂ := row.interval.min .φ₂ / N
           α := row.A_min / N}
  max := { θ₁ := row.interval.max .θ₁ / N
           θ₂ := row.interval.max .θ₂ / N
           φ₁ := row.interval.max .φ₁ / N
           φ₂ := row.interval.max .φ₂ / N
           α := row.A_max / N}
