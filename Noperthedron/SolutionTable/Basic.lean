import Noperthedron.SolutionTable.Defs
import Noperthedron.PoseInterval
import Noperthedron.Checker.Global
import Noperthedron.Checker.Local

namespace Noperthedron.Solution

def _root_.Pose.getParam (q : Pose) : Param → ℝ
| .θ₁ => q.θ₁
| .φ₁ => q.φ₁
| .θ₂ => q.θ₂
| .φ₂ => q.φ₂
| .α => q.α

@[mk_iff]
structure Row.ValidSplitParam (tab : Table) (row : Row) (param : Param) : Prop where
  bound0 : row.ID < row.IDfirstChild
  bound1 : row.IDfirstChild < Array.size tab
  bound2 : row.IDfirstChild + 1 < Array.size tab
  first_child_good : tab[row.IDfirstChild].interval = row.interval.lower_half param
  second_child_good : tab[row.IDfirstChild + 1].interval = row.interval.upper_half param

instance (tab : Table) (row : Row) (param : Param) : Decidable (Row.ValidSplitParam tab row param) :=
  decidable_of_iff _ (Row.validSplitParam_iff tab row param).symm

def Row.ValidBinarySplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 2 ∧
    ((row.split = 1 ∧ row.ValidSplitParam tab .θ₁) ∨
     (row.split = 2 ∧ row.ValidSplitParam tab .φ₁) ∨
     (row.split = 3 ∧ row.ValidSplitParam tab .θ₂) ∨
     (row.split = 4 ∧ row.ValidSplitParam tab .φ₂) ∨
     (row.split = 5 ∧ row.ValidSplitParam tab .α))
deriving Decidable

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

@[mk_iff]
inductive Row.Valid (tab : Table) (row : Row) : Prop where
  | asSplit : row.ValidSplit tab → Row.Valid tab row
  | asGlobal : row.ValidGlobal → Row.Valid tab row
  | asLocal : row.ValidLocal → Row.Valid tab row

instance (tab : Table) (row : Row) : Decidable (Row.Valid tab row) :=
  decidable_of_iff _ (Row.valid_iff tab row).symm

/-- A row is well-formed when its rational interval has `min ≤ max` componentwise. -/
abbrev Row.WellFormed (row : Row) : Prop := row.interval.WellFormed

def Row.ValidIx (tab : Table) (i : ℕ) (row : Row) : Prop :=
  row.ID = i ∧ row.Valid tab ∧ row.ID < tab.size ∧ row.WellFormed
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

/-- The minimum endpoint of an `Interval`, viewed as a `Pose` (each coordinate divided
    by the common denominator `DENOM`). -/
noncomputable
def Interval.minPose (iv : Interval) : Pose where
  θ₁ := iv.min .θ₁ / DENOM
  θ₂ := iv.min .θ₂ / DENOM
  φ₁ := iv.min .φ₁ / DENOM
  φ₂ := iv.min .φ₂ / DENOM
  α := iv.min .α / DENOM

/-- The maximum endpoint of an `Interval`, viewed as a `Pose`. -/
noncomputable
def Interval.maxPose (iv : Interval) : Pose where
  θ₁ := iv.max .θ₁ / DENOM
  θ₂ := iv.max .θ₂ / DENOM
  φ₁ := iv.max .φ₁ / DENOM
  φ₂ := iv.max .φ₂ / DENOM
  α := iv.max .α / DENOM

private lemma Interval.minPose_le_maxPose {iv : Interval} (h : iv.WellFormed) :
    iv.minPose ≤ iv.maxPose := by
  rw [Pose.le_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Interval.minPose, Interval.maxPose]
     exact div_le_div_of_nonneg_right (by exact_mod_cast h _) (by norm_num [DENOM]))

noncomputable
def Interval.toPoseInterval (iv : Interval) (h : iv.WellFormed) : PoseInterval :=
  PoseInterval.mk iv.minPose iv.maxPose (iv.minPose_le_maxPose h)

noncomputable
def Row.toPoseInterval (row : Row) (h : row.interval.WellFormed) : PoseInterval :=
  row.interval.toPoseInterval h

/-- The set of poses lying in the rational interval (regardless of well-formedness;
    if `iv` is not well-formed this is empty along the offending axis). Defined directly
    as `Set.Icc` of the min/max endpoints so it does not depend on a well-formedness
    hypothesis, agreeing definitionally with `iv.toPoseInterval h` whenever `h` exists. -/
noncomputable
instance : Coe Interval (Set Pose) where
  coe iv := Set.Icc iv.minPose iv.maxPose

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
      simp_all
    else
      replace h := Nat.le_of_not_lt h
      have : (i : ℕ) - ivs1.length < ivs2.length := by grind
      specialize h2 ⟨(i : ℕ) - ivs1.length, this⟩
      simp_all
