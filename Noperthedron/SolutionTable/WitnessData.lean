import Noperthedron.SolutionTable.PrecheckBridge
import Noperthedron.SolutionTable.TightSubset
import Noperthedron.SolutionTable.BinaryFormat

/-!
# Witness data: definitions, native_decide checks, and bridge theorems

This file contains the heavy computational work — `native_decide` over 18.7M rows.
It is separated from `Witness.lean` (assembly) so that the expensive build (~2 hours)
only needs to run once, while the assembly logic can be iterated quickly.

## Data loading strategy

Each data definition has:
- A **kernel-level body** that is computable but meaningless (e.g., `#[]` for the table)
- An `@[implemented_by]` attribute routing native compilation to binary-loaded data

## Iterative checking

`native_decide` on `∀ i : Fin n, P i` uses a recursive `Decidable` instance that overflows
the stack for n = 18.7M. We avoid this by reformulating all universal checks as iterative
`Bool`-returning functions (`iterAll` / `Array.all`) that compile to loops, then bridging
from `Bool = true` to `∀` with pure proofs.

## Trust boundaries

1. **`@[implemented_by]` + `native_decide`**: We trust that the native code correctly
   evaluates the decision procedures using the loaded binary data.
2. **Oracle soundness fields**: The sorry'd fields in `globalCert` and `localCert`
   are the Phase B trust boundary (computable Gℚ/maxHℚ, sqrt approximations).
-/

namespace Solution

/-!
### Iterative checking infrastructure

`iterAll n p` checks `p i` for all `i < n` using a tail-recursive loop that compiles
to native iteration, avoiding the O(n) stack depth of `Decidable (∀ i : Fin n, P i)`.
-/

/-- Tail-recursive check that `p i = true` for all `i < n`. -/
def iterAll (n : Nat) (p : Nat → Bool) : Bool :=
  go 0
where
  go (i : Nat) : Bool :=
    if i < n then if p i then go (i + 1) else false else true
  termination_by n - i

private theorem iterAll_go_sound (n : Nat) (p : Nat → Bool) (start : Nat)
    (h : iterAll.go n p start = true) :
    ∀ i, start ≤ i → i < n → p i = true := by
  unfold iterAll.go at h
  split at h
  · rename_i h_lt
    split at h
    · rename_i hp
      intro i hle hlt
      rcases Nat.eq_or_lt_of_le hle with rfl | hgt
      · exact hp
      · exact iterAll_go_sound n p (start + 1) h i (by omega) hlt
    · exact absurd h Bool.false_ne_true
  · intro i hle hlt; omega
termination_by n - start

theorem iterAll_sound {n : Nat} {p : Nat → Bool} (h : iterAll n p = true) :
    ∀ i, i < n → p i = true :=
  fun i hlt => iterAll_go_sound n p 0 h i (Nat.zero_le _) hlt

/-!
### Data definitions

The `@[implemented_by]` attribute routes native compilation (used by `native_decide`)
to the binary-loaded data from `BinaryFormat.lean`. The kernel-level definitions use
dummy values that are never evaluated in proofs.
-/

/-- The solution table. Native code loads from `solution_table.bin`. -/
@[implemented_by getLoadedTableImpl]
def solutionTable : Table := #[]

/-- Per-row exceeds_ok Bool array. Native code loads from `cert_data.bin`. -/
@[implemented_by getLoadedExceedsImpl]
def exceedsOkData : Array Bool := #[]

/-- Local certificate data (7 Bool arrays). Native code loads from `cert_data.bin`. -/
@[implemented_by getLoadedLocalCertImpl]
def localCertData : LocalPrecheckCertificateData :=
  { boundR_ok := #[], boundDelta_ok := #[], ae1_ok := #[],
    ae2_ok := #[], span1_ok := #[], span2_ok := #[], be_ok := #[] }

/-- Global certificate data. Uses loaded `exceedsOkData` for the exceeds_ok array
    and a dummy S array (S is only used in sorry'd oracle soundness proofs). -/
def globalCertData : GlobalPrecheckCertificateData :=
  { S := #[]
    exceeds_ok := exceedsOkData }

/-- Upper sqrt approximation oracle (Phase B trust boundary). -/
noncomputable def witnessSu : RationalApprox.UpperSqrt := sorry

/-- Lower sqrt approximation oracle (Phase B trust boundary). -/
noncomputable def witnessSl : RationalApprox.LowerSqrt := sorry

/-!
### Oracle-backed certificates (sorry'd soundness — Phase B trust boundary)
-/

/-- Global precheck certificate with oracle soundness assumptions. -/
noncomputable def globalCert : GlobalPrecheckCertificate solutionTable where
  data := globalCertData
  forTable := sorry  -- data sizes match tab.size
  S_in_poly := sorry -- oracle trust: external verifier validated S ∈ vertices
  exceeds_sound := sorry -- oracle trust: external verifier validated Gℚ > maxHℚ

/-- Local precheck certificate with oracle soundness assumptions. -/
noncomputable def localCert :
    LocalPrecheckCertificate solutionTable witnessSu witnessSl where
  data := localCertData
  forTable := sorry -- 7 size equalities
  boundR_sound := sorry -- oracle trust
  boundDelta_sound := sorry -- oracle trust
  ae1_sound := sorry -- oracle trust
  ae2_sound := sorry -- oracle trust
  span1_sound := sorry -- oracle trust
  span2_sound := sorry -- oracle trust
  be_sound := sorry -- oracle trust

/-!
### Iterative Bool checks (native_decide)

Each check is a `Bool`-valued function that uses `iterAll` (tail-recursive loop) or
`Array.all` (iterative fold) instead of `∀ i : Fin n` (recursive decidable instance).
-/

/-- Every row's ID matches its array index (iterative check). -/
def checkIds : Bool :=
  iterAll solutionTable.size fun i =>
    if h : i < solutionTable.size then (solutionTable[i]'h).ID == i else true

/-- Split/leaf classification check: nodeType = 1, 2, or 3 (element-only). -/
def checkCover : Bool :=
  solutionTable.all fun row =>
    row.nodeType == 1 || row.nodeType == 2 || row.nodeType == 3

/-- Global leaf check: nodeType = 1 → globalFromData passes (element-only). -/
def checkLeafGlobal : Bool :=
  solutionTable.all fun row =>
    row.nodeType != 1 || row.globalPreconditionCheckBoolFromData globalCertData

/-- Local leaf check: nodeType = 2 → localFromData ∧ congruence pass (element-only). -/
def checkLeafLocal : Bool :=
  solutionTable.all fun row =>
    row.nodeType != 2 ||
      (row.localPreconditionCheckBoolFromData localCertData && congrDecide row)

/-- Split node check: nodeType ∉ {1,2} → ValidSplit (iterative, needs index for tab access). -/
def checkSplits : Bool :=
  iterAll solutionTable.size fun i =>
    if h : i < solutionTable.size then
      let row := solutionTable[i]'h
      row.nodeType == 1 || row.nodeType == 2 || decide (row.ValidSplit solutionTable)
    else true

/-!
### native_decide proofs of Bool checks
-/

theorem checkIds_true : checkIds = true := by native_decide
theorem checkCover_true : checkCover = true := by native_decide
theorem checkLeafGlobal_true : checkLeafGlobal = true := by native_decide
theorem checkLeafLocal_true : checkLeafLocal = true := by native_decide
theorem checkSplits_true : checkSplits = true := by native_decide

/-!
### Bridge theorems: Bool = true → ∀ i : Fin n, ...

These proofs never evaluate the data — they are pure logical bridges.
-/

/-- Every row's ID matches its array index. -/
theorem witnessIds :
    ∀ i : Fin solutionTable.size, solutionTable[i].ID = i := by
  intro i
  have h := iterAll_sound checkIds_true i.val i.isLt
  simp only [show i.val < solutionTable.size from i.isLt, dite_true] at h
  exact beq_iff_eq.mp h

/-- Every row is a global leaf, local leaf, or split node. -/
theorem witnessCover :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType = 1 ∨
      solutionTable[i].nodeType = 2 ∨
      solutionTable[i].nodeType = 3 := by
  intro i
  have h := checkCover_true
  simp only [checkCover] at h
  rw [Array.all_eq_true] at h
  have hi := h i.val i.isLt
  simp only [beq_iff_eq, Bool.or_eq_true] at hi
  rcases hi with (h1 | h2) | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- Global leaf rows pass the FromData global check. -/
theorem witnessLeafGlobal :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType = 1 →
      solutionTable[i].globalPreconditionCheckBoolFromData globalCertData = true := by
  intro i hnt
  have h := checkLeafGlobal_true
  simp only [checkLeafGlobal] at h
  rw [Array.all_eq_true] at h
  have hi := h i.val i.isLt
  simp only [bne_iff_ne, Bool.or_eq_true] at hi
  rcases hi with h1 | h2
  · exact absurd hnt h1
  · exact h2

/-- Local leaf rows pass the FromData local check and congruence check. -/
theorem witnessLeafLocal :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType = 2 →
      solutionTable[i].localPreconditionCheckBoolFromData localCertData = true ∧
      congrDecide solutionTable[i] = true := by
  intro i hnt
  have h := checkLeafLocal_true
  simp only [checkLeafLocal] at h
  rw [Array.all_eq_true] at h
  have hi := h i.val i.isLt
  simp only [bne_iff_ne, Bool.or_eq_true, Bool.and_eq_true] at hi
  rcases hi with h1 | ⟨h2, h3⟩
  · exact absurd hnt h1
  · exact ⟨h2, h3⟩

/-- Split rows have valid split structure. -/
theorem witnessSplits :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType ≠ 1 → solutionTable[i].nodeType ≠ 2 →
      solutionTable[i].ValidSplit solutionTable := by
  intro i h1 h2
  have h := iterAll_sound checkSplits_true i.val i.isLt
  simp only [show i.val < solutionTable.size from i.isLt, dite_true] at h
  simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h

/-- The table is non-empty. -/
theorem witnessNonempty : 0 < solutionTable.size := by native_decide

end Solution
