import Noperthedron.SolutionTable.Basic
import Noperthedron.Checker.RowZero

/-!
# Assembling a `ValidTable` from getter-based chunk checks

The kernel-only route loads the 2M-row solution table as many chunk
definitions and validates them with `decide +kernel` theorems (see
`SolutionTable/Load.lean`). The sticking point is *random access*: split rows
reference their children via `tab[row.IDfirstChild + n]`, and reducing a flat
2M-entry `Array`/`List` literal index under the kernel costs O(index) per
access. So the kernel never sees the `Array` at all:

* Validity is restated against an abstract getter `get : ℕ → Row`
  (`Row.ValidSplitParamAt`, …, `Row.ValidIxAt`), decidably. The getter is
  realized as a digit-curried dispatch over chunk constants
  (`rowGetter`, built by `assemble_row_dispatch` in `Load.lean`), so one
  access walks ≤ 32 `Matrix.vecCons` cells plus one ≤ chunkSize list walk.
* Range theorems prove `RangeOk get size a b` by `decide +kernel`;
  `RangeOk.append` folds them, and `validIxAt_of_rangeOk` turns full
  coverage into `∀ i : Fin size, Row.ValidIxAt get size i`.
* At the `Prop` level only, `tableOfGetter get size := Array.ofFn …` gives an
  actual `Table`; `Array.getElem_ofFn` is a *rewrite* (the kernel never
  reduces the array), and `validTableOfGetter` produces the `ValidTable` the
  main theorem consumes.
-/

namespace Noperthedron.Solution

/-! ## Validity against an abstract getter

These mirror `Row.ValidSplitParam`, `Table.HasIntervals`,
`Row.ValidSingleParamSplit`, `Row.ValidFullSplit`, `Row.ValidSplit`,
`Row.Valid` and `Row.ValidIx` from `SolutionTable/Basic.lean`, with the table
replaced by `get : ℕ → Row` and `size : ℕ`. -/

@[mk_iff]
structure Row.ValidSplitParamAt (get : ℕ → Row) (size : ℕ) (row : Row)
    (param : Param) : Prop where
  id_in_table : row.ID < row.IDfirstChild
  children_in_table : row.IDfirstChild + row.nrChildren ≤ size
  nonzero_children : row.nrChildren ≠ 0
  children_intervals_good : ∀ n : Fin row.nrChildren,
    (get (row.IDfirstChild + n)).interval =
      row.interval.nth_part param row.nrChildren (hN := ⟨nonzero_children⟩) n

instance (get : ℕ → Row) (size : ℕ) (row : Row) (param : Param) :
    Decidable (Row.ValidSplitParamAt get size row param) :=
  decidable_of_iff _ (Row.validSplitParamAt_iff get size row param).symm

def HasIntervalsAt (get : ℕ → Row) (size : ℕ) (start : ℕ)
    (intervals : List Interval) : Prop :=
  ∀ i : Fin intervals.length,
    start + i.val < size ∧ (get (start + i.val)).interval = intervals[i]
deriving Decidable

def Row.ValidSingleParamSplitAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop :=
  ∃ p, Param.ofSplitCode? row.split = some p ∧ row.ValidSplitParamAt get size p

instance (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidSingleParamSplitAt get size) := by
  unfold Row.ValidSingleParamSplitAt
  generalize Param.ofSplitCode? row.split = code
  cases code with
  | none => exact .isFalse (by simp)
  | some p => exact decidable_of_iff (row.ValidSplitParamAt get size p) (by simp)

def Row.ValidFullSplitAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop :=
  row.nrChildren = 32 ∧ row.split = 6 ∧ row.IDfirstChild > row.ID ∧
  HasIntervalsAt get size row.IDfirstChild
    (cubeFold [Interval.lower_half, Interval.upper_half] row.interval Param.splitOrder)
deriving Decidable

def Row.ValidSplitAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop :=
  (row.nodeType = (3 : ℕ)) ∧
  (row.ValidSingleParamSplitAt get size ∨ row.ValidFullSplitAt get size)
deriving Decidable

def Row.ValidAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop :=
  row.ValidSplitAt get size ∨ row.ValidGlobal ∨ row.ValidLocal
deriving Decidable

def Row.ValidIxAt (get : ℕ → Row) (size : ℕ) (i : ℕ) : Prop :=
  (get i).ID = i ∧ (get i).ValidAt get size ∧ i < size
deriving Decidable

/-! ## Bridges to the `Table`-based predicates

One direction suffices: getter-based validity transfers to any table that
agrees with the getter on `[0, size)`. -/

section Bridge

variable {tab : Table} {get : ℕ → Row} {size : ℕ}
  (hsize : tab.size = size)
  (hget : ∀ i, (h : i < tab.size) → tab[i] = get i)

include hsize hget

theorem Row.ValidSplitParamAt.toTable {row : Row} {param : Param}
    (h : row.ValidSplitParamAt get size param) : row.ValidSplitParam tab param := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by omega, h3, fun n => ?_⟩
  have hn : row.IDfirstChild + n < tab.size := by have := n.isLt; omega
  rw [hget _ hn]
  exact h4 n

theorem HasIntervalsAt.toTable {start : ℕ} {ivs : List Interval}
    (h : HasIntervalsAt get size start ivs) : tab.HasIntervals start ivs := by
  intro i
  obtain ⟨hlt, heq⟩ := h i
  have hlt' : start + i.val < tab.size := by omega
  exact ⟨hlt', by rw [hget _ hlt']; exact heq⟩

theorem Row.ValidSingleParamSplitAt.toTable {row : Row}
    (h : row.ValidSingleParamSplitAt get size) : row.ValidSingleParamSplit tab := by
  obtain ⟨p, hp, hv⟩ := h
  exact ⟨p, hp, hv.toTable hsize hget⟩

theorem Row.ValidFullSplitAt.toTable {row : Row}
    (h : row.ValidFullSplitAt get size) : row.ValidFullSplit tab := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4.toTable hsize hget⟩

theorem Row.ValidSplitAt.toTable {row : Row}
    (h : row.ValidSplitAt get size) : row.ValidSplit tab := by
  obtain ⟨h1, h2 | h2⟩ := h
  · exact ⟨h1, .inl (h2.toTable hsize hget)⟩
  · exact ⟨h1, .inr (h2.toTable hsize hget)⟩

theorem Row.ValidAt.toTable {row : Row}
    (h : row.ValidAt get size) : row.Valid tab := by
  rcases h with h | h | h
  · exact .asSplit (h.toTable hsize hget)
  · exact .asGlobal h
  · exact .asLocal h

/-- Getter-based validity of every index below `size` yields `Table.RowsValid`
for any table of that size agreeing with the getter. -/
theorem Table.rowsValid_of_validIxAt
    (h : ∀ i : Fin size, Row.ValidIxAt get size i) : tab.RowsValid := by
  intro i
  obtain ⟨h1, h2, h3⟩ := h ⟨i.val, hsize ▸ i.isLt⟩
  have hgi : tab[i] = get i.val := hget i.val i.isLt
  refine ⟨by rw [hgi]; exact h1, ?_, by rw [hgi, h1]; exact i.isLt⟩
  rw [hgi]
  exact h2.toTable hsize hget

end Bridge

/-! ## Parallel Bool checker (for the `native_decide` route)

One `native_decide` on `rowsValidIxAtParB get size nTasks` discharges the
same `∀ i : Fin size, Row.ValidIxAt get size i` hypothesis that the kernel
route assembles chunk-by-chunk, with the row checks split into `nTasks`
concurrent `Task.spawn`s. Since `Task.spawn fn` is *definitionally*
`⟨fn ()⟩`, the parallelism is invisible to the logic, and correctness is
proved exactly as for a sequential checker. The loops are `Fin.foldl`, which
compiles flat (the auto-derived `Nat.decidableBallLT` instances are
structurally recursive and overflow the runtime stack on tables with
millions of rows). -/

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

theorem task_get_spawn {α : Type} (fn : Unit → α) (prio : Task.Priority) :
    (Task.spawn fn prio).get = fn () := rfl

/-- `Row.ValidIxAt` as a `Bool`, vacuously `true` past `size` (chunks may
overhang the end). -/
def validIxAtB (get : ℕ → Row) (size i : ℕ) : Bool :=
  if i < size then decide (Row.ValidIxAt get size i) else true

theorem validIxAtB_eq_true_iff (get : ℕ → Row) (size i : ℕ) :
    validIxAtB get size i = true ↔ (i < size → Row.ValidIxAt get size i) := by
  unfold validIxAtB
  split
  · rename_i h
    rw [decide_eq_true_iff]
    exact ⟨fun hv _ => hv, fun hv => hv h⟩
  · rename_i h
    simp only [true_iff]
    exact fun h' => absurd h' h

/-- Check `validIxAtB` on indices `[start, start + cnt)`, as a flat
`Fin.foldl` loop. -/
def chunkValidIxAtB (get : ℕ → Row) (size start cnt : ℕ) : Bool :=
  Fin.foldl cnt (init := true) fun acc j => acc && validIxAtB get size (start + j.val)

theorem chunkValidIxAtB_eq_true_iff (get : ℕ → Row) (size start cnt : ℕ) :
    chunkValidIxAtB get size start cnt = true ↔
      ∀ k, start ≤ k → k < start + cnt → validIxAtB get size k = true := by
  unfold chunkValidIxAtB
  rw [Fin.foldl_and_eq_true_iff (fun j => validIxAtB get size (start + j.val))]
  constructor
  · intro h k hk1 hk2
    have := h ⟨k - start, by omega⟩
    rwa [Nat.add_sub_cancel' hk1] at this
  · intro h j
    exact h (start + j.val) (Nat.le_add_right _ _) (by have := j.isLt; omega)

/-- Check `Row.ValidIxAt` on all of `[0, size)`, split into `nTasks` chunks of
size `chunkSize` running concurrently via `Task.spawn`. The leading `decide`
guard ensures the chunks cover everything, so soundness holds for arbitrary
`nTasks`/`chunkSize`. -/
def rowsValidIxAtChunkedB (get : ℕ → Row) (size nTasks chunkSize : ℕ) : Bool :=
  decide (size ≤ nTasks * chunkSize) &&
    (((List.range nTasks).map fun t =>
        Task.spawn fun _ => chunkValidIxAtB get size (t * chunkSize) chunkSize).all Task.get)

theorem validIxAt_of_rowsValidIxAtChunkedB {get : ℕ → Row} {size nTasks chunkSize : ℕ}
    (h : rowsValidIxAtChunkedB get size nTasks chunkSize = true) :
    ∀ i : Fin size, Row.ValidIxAt get size i := by
  unfold rowsValidIxAtChunkedB at h
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  intro i
  have hc0 : 0 < chunkSize := by
    rcases Nat.eq_zero_or_pos chunkSize with hc | hc
    · subst hc; have := i.isLt; omega
    · exact hc
  have ht : (i : ℕ) / chunkSize < nTasks :=
    (Nat.div_lt_iff_lt_mul hc0).mpr (lt_of_lt_of_le i.isLt hsize)
  have hchunk : chunkValidIxAtB get size ((i : ℕ) / chunkSize * chunkSize) chunkSize = true := by
    have := hall _ (List.mem_map.mpr ⟨(i : ℕ) / chunkSize, List.mem_range.mpr ht, rfl⟩)
    rwa [task_get_spawn] at this
  rw [chunkValidIxAtB_eq_true_iff] at hchunk
  have hk : validIxAtB get size (i : ℕ) = true := by
    have hdm := Nat.div_add_mod (i : ℕ) chunkSize
    have hm := Nat.mod_lt (i : ℕ) hc0
    rw [Nat.mul_comm] at hdm
    exact hchunk (i : ℕ) (by omega) (by omega)
  rw [validIxAtB_eq_true_iff] at hk
  exact hk i.isLt

/-- Parallel analogue over near-equal chunks; `nTasks` should comfortably
exceed the core count for load balancing. -/
def rowsValidIxAtParB (get : ℕ → Row) (size nTasks : ℕ) : Bool :=
  rowsValidIxAtChunkedB get size nTasks (size / nTasks + 1)

theorem validIxAt_of_rowsValidIxAtParB {get : ℕ → Row} {size nTasks : ℕ}
    (h : rowsValidIxAtParB get size nTasks = true) :
    ∀ i : Fin size, Row.ValidIxAt get size i :=
  validIxAt_of_rowsValidIxAtChunkedB h

/-! ## Combining per-range lemmas (for the kernel route)

`RangeOk get size a b` is the statement the generated validation files prove
by `decide +kernel`, one range per declaration. The spans are sized
adaptively because kernel memory per row varies ~10× between row types
(locals build far larger term caches than globals). The generated combine
files fold the ranges with `RangeOk.append`, and full coverage discharges
the `∀ i : Fin size` hypothesis via `validIxAt_of_rangeOk`. -/

/-- Rows `[a, b) ∩ [0, size)` are valid (getter-based). -/
def RangeOk (get : ℕ → Row) (size a b : ℕ) : Prop :=
  ∀ j : Fin (b - a), a + j.val < size → Row.ValidIxAt get size (a + j.val)
deriving Decidable

theorem rangeOk_refl (get : ℕ → Row) (size a : ℕ) : RangeOk get size a a :=
  fun j => absurd j.isLt (by omega)

theorem RangeOk.append {get : ℕ → Row} {size a b c : ℕ} (hab : a ≤ b)
    (h1 : RangeOk get size a b) (h2 : RangeOk get size b c) :
    RangeOk get size a c := by
  intro j hj
  rcases Nat.lt_or_ge (a + j.val) b with h | h
  · exact h1 ⟨j.val, by omega⟩ hj
  · have hji := j.isLt
    have hlt : a + j.val - b < c - b := by omega
    have hsz : b + (a + j.val - b) < size := by omega
    have := h2 ⟨a + j.val - b, hlt⟩ hsz
    simpa [Nat.add_sub_cancel' h] using this

theorem validIxAt_of_rangeOk {get : ℕ → Row} {size : ℕ}
    (h : RangeOk get size 0 size) : ∀ i : Fin size, Row.ValidIxAt get size i := by
  intro i
  simpa using h ⟨i.val, by omega⟩ (by omega)

/-! ## The table, at the `Prop` level only

`tableOfGetter` is never reduced by the kernel: everything the proofs need
about it comes from `Array.size_ofFn` and `Array.getElem_ofFn` rewrites. -/

noncomputable def tableOfGetter (get : ℕ → Row) (size : ℕ) : Table :=
  Array.ofFn (n := size) fun i => get i.val

@[simp] theorem tableOfGetter_size (get : ℕ → Row) (size : ℕ) :
    (tableOfGetter get size).size = size :=
  Array.size_ofFn

theorem tableOfGetter_get (get : ℕ → Row) (size : ℕ) (i : ℕ)
    (h : i < (tableOfGetter get size).size) :
    (tableOfGetter get size)[i] = get i := by
  simp [tableOfGetter]

/-- Assemble a `ValidTable` from getter-based facts: positivity, row 0
carrying `rowZero.interval`, and validity of every index. This is the final
consumer of the chunk theorems; the kernel never evaluates the underlying
`Array.ofFn`. -/
noncomputable def validTableOfGetter (get : ℕ → Row) (size : ℕ)
    (hpos : 0 < size)
    (hfirst : (get 0).interval = rowZero.interval)
    (hvalid : ∀ i : Fin size, Row.ValidIxAt get size i) : ValidTable where
  table := tableOfGetter get size
  rows_valid :=
    Table.rowsValid_of_validIxAt (tableOfGetter_size get size)
      (fun i h => tableOfGetter_get get size i h) hvalid
  nonempty := by simpa using hpos
  contains_tightInterval := by
    rw [show (((tableOfGetter get size)[0]'(by simpa using hpos)).interval :
          Set (Pose ℝ)) = (rowZero.interval : Set (Pose ℝ)) from by
      rw [tableOfGetter_get get size 0 (by simpa using hpos), hfirst]]
    exact rowZero_contains_tightInterval

/-- Runtime analogue of `validTableOfGetter` for a concrete parsed table:
the checks are stated against the getter `fun j => tab[j]!`, and the table
itself is the carrier, so (unlike `validTableOfGetter`) the definition is
computable and the `constructValidTable` executable can construct the value.
Together with `validIxAt_of_rowsValidIxAtParB`, this makes that executable a
native dry run of exactly the checks that `NativeCaseAnalysis` puts under
`native_decide`. -/
def validTableOfParsedChecks (tab : Table)
    (hpos : 0 < tab.size)
    (hfirst : tab[0].interval = rowZero.interval)
    (hvalid : ∀ i : Fin tab.size, Row.ValidIxAt (fun j => tab[j]!) tab.size i) :
    ValidTable where
  table := tab
  rows_valid := Table.rowsValid_of_validIxAt rfl
    (fun i h => (getElem!_pos tab i h).symm) hvalid
  nonempty := hpos
  contains_tightInterval := by
    rw [show (tab[0].interval : Set (Pose ℝ)) = (rowZero.interval : Set (Pose ℝ))
        from by rw [hfirst]]
    exact rowZero_contains_tightInterval

/-! ## The concrete getter shape

`assemble_row_dispatch` (in `SolutionTable/Load.lean`) builds a digit-curried
`Fin 8 → Fin 8 → Fin 8 → Fin 8 → List Row` dispatch over up to 4096 loaded
chunk constants; `rowGetter` turns it into the `ℕ → Row` getter. A kernel
access costs ≤ 32 `Matrix.vecCons` cells for the dispatch walk plus at most
`chunkSize` `List` cells within the chunk. -/

/-- The `O(log)` getter over a curried dispatch
(`assemble_row_dispatch_curried`): seven `Fin 8` digit steps, no `List`
walk. -/
def rowGetterC
    (dispatch : Fin 8 → Fin 8 → Fin 8 → Fin 8 → (Fin 8 → Fin 8 → Fin 8 → Row))
    (i : ℕ) : Row :=
  let k := i / 512
  let j := i % 512
  dispatch ⟨k / 512 % 8, Nat.mod_lt _ (by norm_num)⟩
           ⟨k / 64 % 8, Nat.mod_lt _ (by norm_num)⟩
           ⟨k / 8 % 8, Nat.mod_lt _ (by norm_num)⟩
           ⟨k % 8, Nat.mod_lt _ (by norm_num)⟩
           ⟨j / 64 % 8, Nat.mod_lt _ (by norm_num)⟩
           ⟨j / 8 % 8, Nat.mod_lt _ (by norm_num)⟩
           ⟨j % 8, Nat.mod_lt _ (by norm_num)⟩

def rowGetter (dispatch : Fin 8 → Fin 8 → Fin 8 → Fin 8 → List Row)
    (chunkSize : ℕ) (i : ℕ) : Row :=
  let k := i / chunkSize
  (dispatch ⟨k / 512 % 8, Nat.mod_lt _ (by norm_num)⟩
            ⟨k / 64 % 8, Nat.mod_lt _ (by norm_num)⟩
            ⟨k / 8 % 8, Nat.mod_lt _ (by norm_num)⟩
            ⟨k % 8, Nat.mod_lt _ (by norm_num)⟩).getD (i % chunkSize) default

/-! ## Smoke tests -/

/-- A 1-row table consisting of a known-valid global leaf. -/
private def testTinyTable : Table := #[{ testGlobalRow with ID := 0 }]

-- The parallel checker accepts a valid table (with the 512 chunks vastly
-- overhanging the 1-row table) and agrees with the sequential decision
-- procedure for `Row.ValidIxAt`.
/-- info: (true, true) -/
#guard_msgs in
#eval (rowsValidIxAtParB (fun j => testTinyTable[j]!) testTinyTable.size 512,
       decide (∀ i : Fin testTinyTable.size,
         Row.ValidIxAt (fun j => testTinyTable[j]!) testTinyTable.size i))

-- Degenerate parameters: zero tasks must fail the coverage guard for a
-- positive size, and must accept size zero.
/-- info: (false, true) -/
#guard_msgs in
#eval (rowsValidIxAtParB (fun j => testTinyTable[j]!) testTinyTable.size 0,
       rowsValidIxAtParB (fun j => testTinyTable[j]!) 0 0)

end Noperthedron.Solution
