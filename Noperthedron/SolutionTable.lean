import Mathlib.Data.Real.Basic
import Noperthedron.PoseInterval

namespace Solution

/--
A `Solution.Row` aims to closely model of exactly the data in Steininger and Yurkevich's big CSV file.
IDs start from zero. See [SY25] §7.1 for the meaning of all these fields.
-/
structure Row : Type where
   ID : ℕ
   nodeType : ℕ
   hnt : nodeType ∈ ({1, 2, 3} : Finset ℕ)
   nrChildren : ℕ
   IDfirstChild : ℕ
   split : ({1, 2, 3, 4, 5, 6} : Finset ℕ)
   T1_min : ℕ
   T1_max : ℕ
   V1_min : ℕ
   V1_max : ℕ
   T2_min : ℕ
   T2_max : ℕ
   V2_min : ℕ
   V2_max : ℕ
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
   sigma_Q : ({-1, 1} : Finset ℤ)

abbrev Table : Type := Array Row

/-
Do we want to write this validity checker instead as a manifestly
computational program returning Bool?
-/

def Row.ValidGlobal (tab : Table) (row : Row) : Prop :=
  (row.nodeType = (1 : ℕ)) ∧ sorry

def Row.ValidLocal (tab : Table) (row : Row) : Prop :=
  (row.nodeType = (2 : ℕ)) ∧ sorry

def Row.ValidSplit (tab : Table) (row : Row) : Prop :=
  (row.nodeType = (3 : ℕ)) ∧ sorry

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
  min := { θ₁ := row.T1_min / N
           θ₂ := row.T2_min / N
           φ₁ := row.V1_min / N
           φ₂ := row.V2_min / N
           α := row.A_min / N}
  max := { θ₁ := row.T1_max / N
           θ₂ := row.T2_max / N
           φ₁ := row.V1_max / N
           φ₂ := row.V2_max / N
           α := row.A_max / N}
