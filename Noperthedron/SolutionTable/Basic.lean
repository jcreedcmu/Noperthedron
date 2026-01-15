import Mathlib.Data.Real.Basic
import Noperthedron.PoseInterval

namespace Solution

inductive Param where | θ₁ | φ₁ | θ₂ | φ₂ | α
deriving BEq, ReflBEq, LawfulBEq, Repr, Fintype

def _root_.Pose.getParam (q : Pose) : Param → ℝ
| .θ₁ => q.θ₁
| .φ₁ => q.φ₁
| .θ₂ => q.θ₂
| .φ₂ => q.φ₂
| .α => q.α

structure Interval where
  min : Param → ℕ
  max : Param → ℕ
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

instance (tab : Table) (row : Row) : Decidable (Row.ValidGlobal tab row) := by
  sorry

def Row.ValidLocal (tab : Table) (row : Row) : Prop :=
  row.nodeType = 2 ∧ sorry

instance (tab : Table) (row : Row) : Decidable (Row.ValidLocal tab row) := by
  sorry

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
  bound0 : row.ID < row.IDfirstChild
  bound1 : row.IDfirstChild < Array.size tab
  bound2 : row.IDfirstChild + 1 < Array.size tab
  first_child_good : tab[row.IDfirstChild].interval = row.interval.lower_half param
  second_child_good : tab[row.IDfirstChild + 1].interval = row.interval.upper_half param

instance (tab : Table) (row : Row) (param : Param) : Decidable (Row.ValidSplitParam tab row param) :=
  decidable_of_iff
    (row.split = 1 ∧
     ∃ (bound0 : row.ID < row.IDfirstChild),
     ∃ (bound1 : row.IDfirstChild < Array.size tab),
     ∃ (bound2 : row.IDfirstChild + 1 < Array.size tab),
     tab[row.IDfirstChild].interval = row.interval.lower_half param ∧
     tab[row.IDfirstChild + 1].interval = row.interval.upper_half param)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩,
     fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

def Row.ValidBinarySplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 2 ∧
    ((row.split = 1 ∧ row.ValidSplitParam tab .θ₁) ∨
     (row.split = 2 ∧ row.ValidSplitParam tab .φ₁) ∨
     (row.split = 3 ∧ row.ValidSplitParam tab .θ₂) ∨
     (row.split = 4 ∧ row.ValidSplitParam tab .φ₂) ∨
     (row.split = 5 ∧ row.ValidSplitParam tab .α))
deriving Decidable

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
deriving Decidable

def Row.ValidFullSplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 32 ∧ row.split = 6 ∧ row.IDfirstChild > row.ID ∧
  tab.HasIntervals row.IDfirstChild (cubeFold [Interval.lower_half, Interval.upper_half] row.interval [.θ₁, .φ₁, .θ₂, .φ₂, .α])
deriving Decidable

def Row.ValidSplit (tab : Table) (row : Row) : Prop :=
  (row.nodeType = (3 : ℕ)) ∧ (row.ValidBinarySplit tab ∨ row.ValidFullSplit tab)
deriving Decidable

inductive Row.Valid (tab : Table) (row : Row) : Prop where
  | asSplit : row.ValidSplit tab → Row.Valid tab row
  | asGlobal : row.ValidGlobal tab → Row.Valid tab row
  | asLocal : row.ValidLocal tab → Row.Valid tab row

instance (tab : Table) (row : Row) : Decidable (Row.Valid tab row) := by
  apply decidable_of_iff (row.ValidSplit tab ∨ row.ValidGlobal tab ∨ row.ValidLocal tab)
  constructor
  · intro h; rcases h with h | h | h
    · exact .asSplit h
    · exact .asGlobal h
    · exact .asLocal h
  · exact fun h =>
      match h with
      | Row.Valid.asSplit h => Or.inl h
      | Row.Valid.asGlobal h => Or.inr (Or.inl h)
      | Row.Valid.asLocal h => Or.inr (Or.inr h)

def Row.ValidIx (tab : Table) (i : ℕ) (row : Row) : Prop :=
  row.ID = i ∧ row.Valid tab ∧ row.ID < tab.size
deriving Decidable

def Table.Valid (tab : Table) : Prop :=
  ∀ i : Fin (tab.size), tab[i].ValidIx tab i
deriving Decidable

lemma Table.Valid.valid_at {tab : Table} (htab : tab.Valid) {i : ℕ} (hi : i < tab.size) :
    tab[i].ValidIx tab i := htab ⟨i, hi⟩

def Table.valid_decidable (tab : Table) : Decidable tab.Valid := by
  exact inferInstance

/--
The common denominator of θ₁, θ₂, φ₁, φ₂, α rational
representation in the table. See [SY25 §7.2]
-/
def DENOM : ℝ := 15360000

noncomputable
def Interval.toPoseInterval (iv : Interval) : PoseInterval where
  min := { θ₁ := iv.min .θ₁ / DENOM
           θ₂ := iv.min .θ₂ / DENOM
           φ₁ := iv.min .φ₁ / DENOM
           φ₂ := iv.min .φ₂ / DENOM
           α := iv.min .α / DENOM}
  max := { θ₁ := iv.max .θ₁ / DENOM
           θ₂ := iv.max .θ₂ / DENOM
           φ₁ := iv.max .φ₁ / DENOM
           φ₂ := iv.max .φ₂ / DENOM
           α := iv.max .α / DENOM}

noncomputable
def Row.toPoseInterval (row : Row) : PoseInterval :=
  row.interval.toPoseInterval

instance : Coe Interval (Set Pose) where
  coe iv := { q : Pose | q ∈ iv.toPoseInterval }

lemma cube_fold_nonempty_aux {α β : Type} {fs : List (α → β → β)} (hfs : fs ≠ []) (b : β) (as : List α) :
   0 < (cubeFold fs b as).length := by
  match as with
  | [] => simp [cubeFold]
  | h :: tl =>
    simp only [cubeFold, List.length_flatMap]
    have (f : α → β → β) : 0 < (cubeFold fs (f h b) tl).length := by
      exact cube_fold_nonempty_aux hfs (f h b) tl
    refine List.sum_pos _ ?_ (by simpa using hfs)
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨f, hf1, hf2⟩ := hx
    rw [← hf2]
    exact this f

lemma cube_fold_nonempty {α β : Type} {fs : List (α → β → β)} (hfs : fs ≠ []) (b : β) (as : List α) :
   1 ≤ (cubeFold fs b as).length := cube_fold_nonempty_aux hfs b as

lemma cube_fold_halves (h : Param) (tl : List Param) (iv : Interval)
    (lower : Param → Interval → Interval)
    (upper : Param → Interval → Interval) :
    cubeFold [lower, upper] iv (h :: tl) =
      cubeFold [lower, upper] (lower h iv) tl ++
      cubeFold [lower, upper] (upper h iv) tl := by
  simp [cubeFold]

lemma has_intervals_start_in_table (tab : Table) (n : ℕ) (ivs : List Interval) (hivs : 1 ≤ ivs.length)
    (hi : tab.HasIntervals n ivs) : n < tab.size := by
  unfold Table.HasIntervals at hi
  simpa using (hi ⟨0, Nat.zero_lt_of_lt hivs⟩).1

lemma has_intervals_concat (tab : Table) (start : ℕ) (ivs1 ivs2 : List Interval) :
    tab.HasIntervals start (ivs1 ++ ivs2) ↔
    tab.HasIntervals start ivs1 ∧ tab.HasIntervals (start + ivs1.length) ivs2 := by
  constructor
  · intro hi
    constructor
    · unfold Table.HasIntervals at hi ⊢
      intro i; simpa using hi (Fin.castLE (by simp) i)
    · unfold Table.HasIntervals at hi ⊢
      intro i
      specialize hi ⟨ivs1.length + i, by simp⟩
      simp at hi
      obtain ⟨h, p⟩ := hi
      replace h : start + ivs1.length + (↑i : ℕ) < Array.size tab :=
        by ring_nf at h ⊢; exact h
      use h; ring_nf at p ⊢; exact p
  · rintro ⟨h1, h2⟩
    unfold Table.HasIntervals at h1 h2 ⊢
    intro i
    if h : i < ivs1.length then
      specialize h1 ⟨i, h⟩
      simp only [Fin.getElem_fin] at h1 ⊢
      obtain ⟨h1a, h1b⟩ := h1
      use h1a
      rw [h1b]
      exact List.getElem_append_left' h ivs2
    else
      replace h := Nat.le_of_not_lt h
      have : (i : ℕ) - ivs1.length < ivs2.length := by grind
      specialize h2 ⟨(i : ℕ) - ivs1.length, this⟩
      simp only [Fin.getElem_fin] at h2 ⊢
      obtain ⟨h2a, h2b⟩ := h2
      have : ivs1.length + (↑i - ivs1.length) = i := Nat.add_sub_of_le h
      conv at h2a => lhs; rw [add_assoc, this]
      conv at h2b => lhs; arg 1; arg 2; rw [add_assoc, this]
      use h2a
      rw [h2b]
      rw [List.getElem_append_right h]
