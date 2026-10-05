module

public import Noperthedron.PentagonalHexecontahedron.IsNotRupert
public import Noperthedron.PentagonalHexecontahedron.SparseLocalViewTree

@[expose] public section

/-!
# Native executable proof construction

This module is the executable counterpart of the generated `native_decide`
proofs. A release-mode program can check data-only local and global tables in
parallel, then retain the kernel-proved semantic validity witnesses in
`PLift`. The final `CheckedChartTables.notRupert` value has exactly the public
non-Rupert proposition as its type.

Keeping the proof witnesses in `PLift` lets ordinary `IO` code sequence checks
and report useful errors. Proof fields are erased by native code generation;
their correctness comes from the specifications of the Boolean checkers.
-/

namespace Noperthedron.PentagonalHexecontahedron.NativeExecutable

variable {P : C5Model}

open AtlasProjectiveLocalViewTree
open SparseLocalViewTree

def log (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

/-- Check one sparse shared-local table with native worker tasks and return its
semantic validity proof. -/
def checkLocal (label : String) (taskCount : Nat)
    (table : AtlasProjectiveLocalViewTree.Table) : IO (PLift table.Valid) := do
  let start ← IO.monoNanosNow
  log s!"checking local {label}: {table.size} rows in {taskCount} native tasks"
  let chunkSize := table.size / taskCount + 1
  let tasks := sparseTableTasks table taskCount
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  let mut checkedRows := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    unless valid do
      let first := index * chunkSize
      let afterLast := min table.size (first + chunkSize)
      throw (IO.userError (s!"local table {label} is invalid in rows " ++
        s!"[{first}, {afterLast})"))
    let first := index * chunkSize
    let rowCount := if first < table.size then
      min chunkSize (table.size - first)
    else 0
    completed := completed + 1
    checkedRows := checkedRows + rowCount
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log (s!"local {label}: {checkedRows}/{table.size} rows checked " ++
        s!"in {completed}/{total} completed tasks " ++
        s!"({(now - start) / 1000000} ms)")
  if h : sparseTableValidWithTasksB table taskCount tasks = true then
    let finish ← IO.monoNanosNow
    log s!"valid local {label}: {(finish - start) / 1000000} ms"
    have h' : sparseTableValidWithTasksB table taskCount
        (sparseTableTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨Table.Valid.of_sparseWithTasksB h'⟩
  else
    throw (IO.userError s!"local table {label} is not valid")

/-- Check the shared-local (identity-tube) tables from index `k` on,
threading the validity proofs of the tables already checked. -/
partial def checkLocalFrom (taskCount : Nat)
    (tables : AtlasProjectiveSolutionTree.SharedLocalTables) (k : Nat)
    (hk : ∀ i (h : i < tables.size), i < k → tables[i].Valid) :
    IO (PLift (AtlasProjectiveSolutionTree.SharedLocalValid tables)) := do
  if hlt : k < tables.size then
    let checked ← checkLocal s!"{k}" taskCount tables[k]
    checkLocalFrom taskCount tables (k + 1) (fun i h hik => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hik with h' | h'
      · exact hk i h h'
      · subst h'
        exact checked.down)
  else
    pure ⟨fun i h => hk i h (by omega)⟩

/-- Check every shared-local table (one per code triangle). -/
def checkLocalAll (taskCount : Nat)
    (tables : AtlasProjectiveSolutionTree.SharedLocalTables) :
    IO (PLift (AtlasProjectiveSolutionTree.SharedLocalValid tables)) :=
  checkLocalFrom taskCount tables 0 (fun _ _ h => absurd h (Nat.not_lt_zero _))

/-- Check one data-only global chart table after attaching the already checked
shared-local tables. -/
def checkGlobal (label : String) (taskCount : Nat)
    (table : AtlasProjectiveSolutionTree.Table)
    (hshared : AtlasProjectiveSolutionTree.SharedLocalValid table.sharedLocal) :
    IO (PLift table.Valid) := do
  let start ← IO.monoNanosNow
  log s!"checking chart {label}: {table.size} rows in {taskCount} native tasks"
  let chunkSize := table.size / taskCount + 1
  let tasks := AtlasProjectiveSolutionTree.tableCoreTasks table taskCount
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  let mut checkedRows := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    unless valid do
      let first := index * chunkSize
      let afterLast := min table.size (first + chunkSize)
      throw (IO.userError (s!"chart {label} is invalid in rows " ++
        s!"[{first}, {afterLast})"))
    let first := index * chunkSize
    let rowCount := if first < table.size then
      min chunkSize (table.size - first)
    else 0
    completed := completed + 1
    checkedRows := checkedRows + rowCount
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log (s!"chart {label}: {checkedRows}/{table.size} rows checked " ++
        s!"in {completed}/{total} completed tasks " ++
        s!"({(now - start) / 1000000} ms)")
  if h : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
      table taskCount tasks = true then
    let finish ← IO.monoNanosNow
    log s!"valid chart {label}: {(finish - start) / 1000000} ms"
    have h' : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
        table taskCount
        (AtlasProjectiveSolutionTree.tableCoreTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨AtlasProjectiveSolutionTree.Table.Valid.of_withTasksB hshared h'⟩
  else
    throw (IO.userError s!"global chart table {label} is not valid")

/-- The complete output of the executable checker. -/
structure CheckedChartTables where
  tables : CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table
  charts : ∀ chart, (tables chart).chart = chart
  valid : ∀ chart, (tables chart).Valid
  cover : WedgeCover.coverValid = true

/-- The proof object constructed by a successful executable run: the checked
tables and view cover exclude every centrally symmetric `IModel` (I-orbits within
`modelErrorQ` of the rational vertices) at once. -/
theorem CheckedChartTables.notRupert (checked : CheckedChartTables) :
    ∀ P : IModel, P.CentrallySymmetric → AtlasProjectiveSolutionTree.ExactClaims P.toC5.polyhedron.hull → ¬ IsRupert P.toC5.verts :=
  fun P hsym hcaps => not_rupert_of_valid_tables P hsym checked.tables checked.charts checked.valid
    checked.cover hcaps

/-- Check all certificate data and construct the final non-Rupert proof.

Generated global data is supplied as a function of the checked shared-local
tables. The two equations prevent an executable wrapper from accidentally
checking the right rows under the wrong chart or shared-local environment. -/
def constructProof (localTaskCount globalTaskCount : Nat)
    (localTables : AtlasProjectiveSolutionTree.SharedLocalTables)
    (globalTables : AtlasProjectiveSolutionTree.SharedLocalTables →
      CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table)
    (hchart : ∀ shared chart, (globalTables shared chart).chart = chart)
    (hshared : ∀ shared chart,
      (globalTables shared chart).sharedLocal = shared) :
    IO (PLift (∀ P : IModel, P.CentrallySymmetric → AtlasProjectiveSolutionTree.ExactClaims P.toC5.polyhedron.hull → ¬ IsRupert P.toC5.verts)) := do
  -- The cover of T by the code triangles (too large for the kernel; see
  -- WedgeCoverData), checked natively like the tables.
  let coverStart ← IO.monoNanosNow
  log "checking the view cover (code triangles cover T)"
  let cover : PLift (WedgeCover.coverValid = true) ←
    if h : WedgeCover.coverValid = true then pure ⟨h⟩
    else throw (IO.userError "the view cover is invalid")
  log s!"view cover valid ({(← IO.monoNanosNow) - coverStart} ns)"
  let checkedLocal ← checkLocalAll localTaskCount localTables
  let shared := localTables
  have sharedValid : AtlasProjectiveSolutionTree.SharedLocalValid shared :=
    checkedLocal.down
  let table0 := globalTables shared 0
  have shared0 : AtlasProjectiveSolutionTree.SharedLocalValid
      table0.sharedLocal := by
    rw [hshared shared 0]
    exact sharedValid
  let valid0 ← checkGlobal "0" globalTaskCount table0 shared0
  let table1 := globalTables shared 1
  have shared1 : AtlasProjectiveSolutionTree.SharedLocalValid
      table1.sharedLocal := by
    rw [hshared shared 1]
    exact sharedValid
  let valid1 ← checkGlobal "1" globalTaskCount table1 shared1
  let table2 := globalTables shared 2
  have shared2 : AtlasProjectiveSolutionTree.SharedLocalValid
      table2.sharedLocal := by
    rw [hshared shared 2]
    exact sharedValid
  let valid2 ← checkGlobal "2" globalTaskCount table2 shared2
  let table3 := globalTables shared 3
  have shared3 : AtlasProjectiveSolutionTree.SharedLocalValid
      table3.sharedLocal := by
    rw [hshared shared 3]
    exact sharedValid
  let valid3 ← checkGlobal "3" globalTaskCount table3 shared3
  let checkedCharts : CheckedChartTables := {
    tables := ![table0, table1, table2, table3]
    charts := by
      intro chart
      fin_cases chart
      · exact hchart shared 0
      · exact hchart shared 1
      · exact hchart shared 2
      · exact hchart shared 3
    valid := by
      intro chart
      fin_cases chart
      · exact valid0.down
      · exact valid1.down
      · exact valid2.down
      · exact valid3.down
    cover := cover.down }
  log "constructed proof: no IModel (I-orbit within 6e-16 of the rational vertices) is Rupert"
  pure ⟨checkedCharts.notRupert⟩

end Noperthedron.PentagonalHexecontahedron.NativeExecutable

end
