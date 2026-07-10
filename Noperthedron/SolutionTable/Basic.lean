import Noperthedron.SolutionTable.Defs
import Noperthedron.PoseInterval
import Noperthedron.Checker.Global
import Noperthedron.Checker.LocalNat
import Noperthedron.Checker.LocalFastNat

namespace Noperthedron.Solution

@[mk_iff]
structure Row.ValidSplitParam (tab : Table) (row : Row) (param : Param) : Prop where
  id_in_table : row.ID < row.IDfirstChild
  children_in_table : row.IDfirstChild + row.nrChildren ≤ Array.size tab
  nonzero_children : row.nrChildren ≠ 0
  children_intervals_good : ∀ (n : Fin row.nrChildren), tab[row.IDfirstChild + n].interval =
    row.interval.nth_part param row.nrChildren (hN := ⟨nonzero_children⟩) n

instance (tab : Table) (row : Row) (param : Param) : Decidable (Row.ValidSplitParam tab row param) :=
  decidable_of_iff _ (Row.validSplitParam_iff tab row param).symm

/-- The row's `split` code selects a single parameter (via `Param.ofSplitCode?`),
and the row is a valid split of its interval along that parameter. -/
def Row.ValidSingleParamSplit (tab : Table) (row : Row) : Prop :=
  ∃ p, Param.ofSplitCode? row.split = some p ∧ row.ValidSplitParam tab p

instance (tab : Table) (row : Row) : Decidable (row.ValidSingleParamSplit tab) := by
  unfold Row.ValidSingleParamSplit
  generalize Param.ofSplitCode? row.split = code
  cases code with
  | none => exact .isFalse (by simp)
  | some p => exact decidable_of_iff (row.ValidSplitParam tab p) (by simp)

def Table.HasIntervals (tab : Table) (start : ℕ) (intervals : List Interval) : Prop :=
  ∀ i : Fin intervals.length,
    ∃ (h : start + i.val < tab.size), tab[start + i.val].interval = intervals[i]
deriving Decidable

def Row.ValidFullSplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 32 ∧ row.split = 6 ∧ row.IDfirstChild > row.ID ∧
  tab.HasIntervals row.IDfirstChild
    (cubeFold [Interval.lower_half, Interval.upper_half] row.interval Param.splitOrder)
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

lemma Table.RowsValid.valid_at {tab : Table} (htab : tab.RowsValid) {i : ℕ} (hi : i < tab.size) :
    tab[i].ValidIx tab i := htab ⟨i, hi⟩

/-- Tail-recursive Bool-valued check that every row of `tab` satisfies `Row.ValidIx`,
backing the manual `Decidable` instance for `Table.RowsValid` below. The auto-derived
instance reduces to `Nat.decidableBallLT`, which is structurally recursive on the table
size and overflows the runtime stack on tables with millions of rows. `Fin.foldl`
compiles to a flat loop, so the runtime stack stays O(1). -/
private def Table.rowsValidB (tab : Table) : Bool :=
  Fin.foldl tab.size (init := true) fun acc i => acc && decide (tab[i].ValidIx tab i)

theorem Fin.foldl_and_factor {n : ℕ} (p : Fin n → Bool) (init : Bool) :
    (Fin.foldl n (fun acc i => acc && p i) init) =
      (init && Fin.foldl n (fun acc i => acc && p i) true) := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Fin.foldl_succ,
        ih (fun i => p i.succ) (init && p 0),
        ih (fun i => p i.succ) (true && p 0)]
    simp [Bool.and_assoc]

theorem Fin.foldl_and_eq_true_iff {n : ℕ} (p : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc && p i) true) = true ↔ ∀ i, p i = true := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Fin.foldl_and_factor]
    simp only [Bool.true_and, Bool.and_eq_true]
    rw [ih (fun i => p i.succ), Fin.forall_fin_succ]

private theorem Table.rowsValidB_eq_true_iff (tab : Table) :
    tab.rowsValidB = true ↔ tab.RowsValid := by
  unfold Table.rowsValidB Table.RowsValid
  rw [Fin.foldl_and_eq_true_iff]
  simp

instance Table.RowsValid.decidable (tab : Table) : Decidable tab.RowsValid :=
  decidable_of_iff _ tab.rowsValidB_eq_true_iff

/-! ### Parallel validity checking

`Table.rowsValidParB` splits the index range into chunks and checks them
concurrently via `Task.spawn`. Since `Task.spawn fn` is *definitionally*
`⟨fn ()⟩`, the parallelism is invisible to the logic, and correctness is proved
exactly as for the sequential checker. This matters for
`NativeCaseAnalysis/ComputationalStep.lean`, where `native_decide` runs this check
over a table with ~18.7 million rows. -/

theorem task_get_spawn {α : Type} (fn : Unit → α) (prio : Task.Priority) :
    (Task.spawn fn prio).get = fn () := rfl

/-- `Row.ValidIx` at index `i` as a `Bool`, vacuously `true` past the end of the
table (chunks are allowed to overhang the end). -/
private def Table.validIxB (tab : Table) (i : ℕ) : Bool :=
  if h : i < tab.size then decide (tab[i].ValidIx tab i) else true

private theorem Table.validIxB_eq_true_iff (tab : Table) (i : ℕ) :
    tab.validIxB i = true ↔ ∀ h : i < tab.size, tab[i].ValidIx tab i := by
  unfold Table.validIxB
  split
  · rename_i h
    rw [decide_eq_true_iff]
    exact ⟨fun hv _ => hv, fun hv => hv h⟩
  · rename_i h
    simp only [true_iff]
    exact fun h' => absurd h' h

/-- Check validity of the rows with indices in `[start, start + cnt)`, as a flat
`Fin.foldl` loop (see `Table.rowsValidB` for why this matters). -/
private def Table.chunkValidB (tab : Table) (start cnt : ℕ) : Bool :=
  Fin.foldl cnt (init := true) fun acc j => acc && tab.validIxB (start + j.val)

private theorem Table.chunkValidB_eq_true_iff (tab : Table) (start cnt : ℕ) :
    tab.chunkValidB start cnt = true ↔
      ∀ k, start ≤ k → k < start + cnt → tab.validIxB k = true := by
  unfold Table.chunkValidB
  rw [Fin.foldl_and_eq_true_iff (fun j => tab.validIxB (start + j.val))]
  constructor
  · intro h k hk1 hk2
    have := h ⟨k - start, by omega⟩
    rwa [Nat.add_sub_cancel' hk1] at this
  · intro h j
    exact h (start + j.val) (Nat.le_add_right _ _) (by have := j.isLt; omega)

/-- Check all rows of the table for validity, splitting the work into `nTasks`
chunks of size `chunkSize` that run concurrently via `Task.spawn`. The leading
`decide` guard ensures that the chunks cover the whole table, so that
`Table.rowsValid_of_rowsValidChunkedB` holds for arbitrary (even nonsensical)
values of `nTasks` and `chunkSize`. -/
def Table.rowsValidChunkedB (tab : Table) (nTasks chunkSize : ℕ) : Bool :=
  decide (tab.size ≤ nTasks * chunkSize) &&
    (((List.range nTasks).map fun t =>
        Task.spawn fun _ => tab.chunkValidB (t * chunkSize) chunkSize).all Task.get)

theorem Table.rowsValid_of_rowsValidChunkedB {tab : Table} {nTasks chunkSize : ℕ}
    (h : tab.rowsValidChunkedB nTasks chunkSize = true) : tab.RowsValid := by
  unfold Table.rowsValidChunkedB at h
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  intro i
  have hc0 : 0 < chunkSize := by
    rcases Nat.eq_zero_or_pos chunkSize with hc | hc
    · subst hc; have := i.isLt; omega
    · exact hc
  have ht : (i : ℕ) / chunkSize < nTasks :=
    (Nat.div_lt_iff_lt_mul hc0).mpr (lt_of_lt_of_le i.isLt hsize)
  have hchunk : tab.chunkValidB ((i : ℕ) / chunkSize * chunkSize) chunkSize = true := by
    have := hall _ (List.mem_map.mpr ⟨(i : ℕ) / chunkSize, List.mem_range.mpr ht, rfl⟩)
    rwa [task_get_spawn] at this
  rw [Table.chunkValidB_eq_true_iff] at hchunk
  have hk : tab.validIxB (i : ℕ) = true := by
    have hdm := Nat.div_add_mod (i : ℕ) chunkSize
    have hm := Nat.mod_lt (i : ℕ) hc0
    rw [Nat.mul_comm] at hdm
    exact hchunk (i : ℕ) (by omega) (by omega)
  rw [Table.validIxB_eq_true_iff] at hk
  exact hk i.isLt

/-- Parallel analogue of `Table.rowsValidB`, splitting the table into `nTasks`
chunks of (near-)equal size. -/
def Table.rowsValidParB (tab : Table) (nTasks : ℕ) : Bool :=
  tab.rowsValidChunkedB nTasks (tab.size / nTasks + 1)

theorem Table.rowsValid_of_rowsValidParB {tab : Table} {nTasks : ℕ}
    (h : tab.rowsValidParB nTasks = true) : tab.RowsValid :=
  Table.rowsValid_of_rowsValidChunkedB h

/--
info: 'Noperthedron.Solution.Table.rowsValid_of_rowsValidParB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Table.rowsValid_of_rowsValidParB

/-- The parallel checker is complete: for a positive number of tasks it agrees
with `Table.RowsValid`. (Soundness, which is the direction the final proof
needs, holds for any `nTasks`; see `Table.rowsValid_of_rowsValidParB`.) -/
theorem Table.rowsValidParB_eq_true_iff {tab : Table} {nTasks : ℕ} (hn : 0 < nTasks) :
    tab.rowsValidParB nTasks = true ↔ tab.RowsValid := by
  refine ⟨Table.rowsValid_of_rowsValidParB, fun hv => ?_⟩
  unfold Table.rowsValidParB Table.rowsValidChunkedB
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  constructor
  · have hdm := Nat.div_add_mod tab.size nTasks
    have hm := Nat.mod_lt tab.size hn
    rw [Nat.mul_succ]
    omega
  · intro b hb
    rw [List.mem_map] at hb
    obtain ⟨t, _, rfl⟩ := hb
    rw [task_get_spawn, Table.chunkValidB_eq_true_iff]
    intro k _ _
    rw [Table.validIxB_eq_true_iff]
    intro hk
    exact hv ⟨k, hk⟩

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
