import Mathlib.Data.Real.Basic
import Noperthedron.PoseInterval

namespace Solution

inductive Param where | θ₁ | φ₁ | θ₂ | φ₂ | α
deriving BEq

structure Interval where
  min : Param → ℕ
  max : Param → ℕ

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

def Interval.lower_half (interval : Interval) (param : Param) : Interval := {
  min := interval.min
  max := fun p => if p == param then (interval.min p + interval.max p)/2 else interval.max p
}

def Interval.upper_half (interval : Interval) (param : Param) : Interval := {
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

def Row.ValidFullSplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 32 ∧ row.split = 6 ∧
    sorry

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
