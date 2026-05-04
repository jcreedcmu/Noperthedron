import Noperthedron.SolutionTable.Defs
import Noperthedron.PoseInterval
import Noperthedron.Checker.Global
import Noperthedron.Checker.Local

namespace Noperthedron.Solution

@[mk_iff]
structure Row.ValidSplitParam (tab : Table) (row : Row) (param : Param) : Prop where
  id_in_table : row.ID < row.IDfirstChild
  children_in_table : row.IDfirstChild + row.nrChildren < Array.size tab
  nonzero_children : row.nrChildren ≠ 0
  children_intervals_good : ∀ (n : Fin row.nrChildren), tab[row.IDfirstChild + n].interval =
    row.interval.nth_part param row.nrChildren (hN := ⟨nonzero_children⟩) n

instance (tab : Table) (row : Row) (param : Param) : Decidable (Row.ValidSplitParam tab row param) :=
  decidable_of_iff _ (Row.validSplitParam_iff tab row param).symm

def Row.ValidSingleParamSplit (tab : Table) (row : Row) : Prop :=
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
  (row.nodeType = (3 : ℕ)) ∧ (row.ValidSingleParamSplit tab ∨ row.ValidFullSplit tab)
deriving Decidable

@[mk_iff]
inductive Row.Valid (tab : Table) (row : Row) : Prop where
  | asSplit : row.ValidSplit tab → Row.Valid tab row
  | asGlobal : row.ValidGlobal → Row.Valid tab row
  | asLocal : row.ValidLocal → Row.Valid tab row

instance (tab : Table) (row : Row) : Decidable (Row.Valid tab row) :=
  decidable_of_iff _ (Row.valid_iff tab row).symm

def Row.ValidIx (tab : Table) (i : ℕ) (row : Row) : Prop :=
  row.ID = i ∧ row.Valid tab ∧ row.ID < tab.size
deriving Decidable

def Table.RowsValid (tab : Table) : Prop :=
  ∀ i : Fin (tab.size), tab[i].ValidIx tab i
deriving Decidable

lemma Table.RowsValid.valid_at {tab : Table} (htab : tab.RowsValid) {i : ℕ} (hi : i < tab.size) :
    tab[i].ValidIx tab i := htab ⟨i, hi⟩

/-- The minimum endpoint of an `Interval`, viewed as a `Pose ℝ` via `Rat.cast`. -/
def Interval.minPose (iv : Interval) : Pose ℝ := iv.min.toReal

/-- The maximum endpoint of an `Interval`, viewed as a `Pose ℝ` via `Rat.cast`. -/
def Interval.maxPose (iv : Interval) : Pose ℝ := iv.max.toReal

private lemma Interval.minPose_le_maxPose (iv : Interval) :
    iv.minPose ≤ iv.maxPose := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (Pose.le_iff iv.min iv.max).mp iv.fst_le_snd
  rw [Pose.le_iff]
  simp only [Interval.minPose, Interval.maxPose, Pose.toReal]
  norm_cast

def Interval.toReal (iv : Interval) : PoseInterval ℝ :=
  PoseInterval.mk iv.minPose iv.maxPose iv.minPose_le_maxPose

def Row.toRealInterval (row : Row) : PoseInterval ℝ :=
  row.interval.toReal

/-- Each component of `iv.toReal.center` (real) is the `Rat.cast` of the corresponding
`iv.center` (rational). -/
lemma Interval.toReal_center_getParam (iv : Interval) (p : Param) :
    iv.toReal.center.getParam p = ((iv.center p : ℚ) : ℝ) := by
  cases p <;>
    simp [Interval.toReal, Interval.minPose, Interval.maxPose, Interval.center,
          PoseInterval.center, PoseInterval.min, PoseInterval.max, Pose.getParam]

@[simp] lemma Interval.toReal_center_θ₁ (iv : Interval) :
    iv.toReal.center.θ₁ = ((iv.center .θ₁ : ℚ) : ℝ) := iv.toReal_center_getParam .θ₁
@[simp] lemma Interval.toReal_center_θ₂ (iv : Interval) :
    iv.toReal.center.θ₂ = ((iv.center .θ₂ : ℚ) : ℝ) := iv.toReal_center_getParam .θ₂
@[simp] lemma Interval.toReal_center_φ₁ (iv : Interval) :
    iv.toReal.center.φ₁ = ((iv.center .φ₁ : ℚ) : ℝ) := iv.toReal_center_getParam .φ₁
@[simp] lemma Interval.toReal_center_φ₂ (iv : Interval) :
    iv.toReal.center.φ₂ = ((iv.center .φ₂ : ℚ) : ℝ) := iv.toReal_center_getParam .φ₂
@[simp] lemma Interval.toReal_center_α (iv : Interval) :
    iv.toReal.center.α = ((iv.center .α : ℚ) : ℝ) := iv.toReal_center_getParam .α

/-- The set of poses lying in the rational interval, defined as `Set.Icc` of the
    min/max endpoints; agrees definitionally with `iv.toReal`. -/
noncomputable
instance : Coe Interval (Set (Pose ℝ)) where
  coe iv := Set.Icc iv.minPose iv.maxPose

structure ValidTable : Type where
  table : Table
  rows_valid : table.RowsValid
  nonempty : 0 < table.size
  contains_tightInterval : (tightInterval : Set (Pose ℝ)) ⊆ (table[0].interval : Set (Pose ℝ))

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
