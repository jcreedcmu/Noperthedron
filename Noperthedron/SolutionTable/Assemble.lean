module

public import Noperthedron.SolutionTable.Basic
public import Noperthedron.Checker.RowZero
-- The test `#eval`s at the bottom interpret Row values at elaboration time.
public meta import Noperthedron.SolutionTable.Defs
public meta import Noperthedron.SolutionTable.Basic

@[expose] public section


/-!
# Assembling a `ValidTable` from chunk checks

The kernel-only route loads the 2M-row solution table as many chunk
definitions and validates them with `decide +kernel` theorems (see
`SolutionTable/Load.lean`). The sticking point is *random access*: split rows
reference their children via `tab[row.IDfirstChild + n]`, and reducing a flat
2M-entry `Array`/`List` literal index under the kernel costs O(index) per
access. So the kernel never sees the `Array` at all:

* Validity is stated once against an abstract getter `get : ℕ → Row`
  (`Row.ValidSplitParamAt`, …, `Row.ValidIxAt`), decidably. The getter is
  realized as a digit-curried dispatch over curried chunk constants
  (`rowGetterC`, built by `assemble_row_dispatch_curried` in `Load.lean`),
  so one access walks ≤ 7 `Fin 8` digit levels — `O(log)`.
* Range theorems prove `RangeOk get size a b` by `decide +kernel`;
  `RangeOk.append` folds them, and `validIxAt_of_rangeOk` turns full
  coverage into `∀ i : Fin size, Row.ValidIxAt get size i`.
* `ValidTable` retains that getter directly, so the checked representation is
  also the representation consumed by the main proof. No intermediate array
  or predicate-conversion layer is needed.
-/

namespace Noperthedron.Solution

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

/-- Assemble a `ValidTable` from getter-based facts: positivity, row 0
carrying `rowZero.interval`, and validity of every index. -/
def validTableOfGetter (get : ℕ → Row) (size : ℕ)
    (hpos : 0 < size)
    (hfirst : (get 0).interval = rowZero.interval)
    (hvalid : ∀ i : Fin size, Row.ValidIxAt get size i) : ValidTable where
  get := get
  size := size
  rows_valid := hvalid
  nonempty := hpos
  contains_tightInterval := by
    rw [hfirst]
    exact rowZero_contains_tightInterval

/-- Specialize `validTableOfGetter` to a parsed array. Together with
`validIxAt_of_rowsValidIxAtParB`, this makes `constructValidTable` a native dry
run of exactly the checks that `NativeCaseAnalysis` puts under
`native_decide`. -/
def validTableOfParsedChecks (tab : Table)
    (hpos : 0 < tab.size)
    (hfirst : tab[0].interval = rowZero.interval)
    (hvalid : ∀ i : Fin tab.size, Row.ValidIxAt (fun j => tab[j]!) tab.size i) :
    ValidTable :=
  validTableOfGetter (fun j => tab[j]!) tab.size hpos (by
    rw [getElem!_pos tab 0 hpos, hfirst]) hvalid

/-! ## The concrete getter shape

`assemble_row_dispatch_curried` (in `SolutionTable/Load.lean`) builds a
digit-curried dispatch over up to 4096 loaded curried chunk constants
(`load_csv_chunks_curried`); `rowGetterC` turns it into the `ℕ → Row`
getter. -/

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

/-! ## Smoke tests -/

/-- A 1-row table consisting of a known-valid global leaf. -/
def testTinyTable : Table := #[{ testGlobalRow with ID := 0 }]

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

end
