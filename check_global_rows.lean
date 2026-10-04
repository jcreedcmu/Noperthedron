import Noperthedron.PentagonalHexecontahedron.NativeExecutable
import Noperthedron.PentagonalHexecontahedron.PackedLocalViewTree
import Noperthedron.PentagonalHexecontahedron.PackedSolutionTree

/-!
Development checker for 5D search packs (pack5d): decodes a
global pack for one chart, with the identity-tube code tables as shared
tables, and checks every row with Lean's row checker
(`AtlasProjectiveSolutionTree.validIxAtB`), reporting the rows that fail.

Unlike `constructPentagonalHexecontahedron`, this works for partial packs (e.g. one job's
tree with its root node as row 0), which are not valid chart tables.

Usage: check_global_rows <chart> <pack | per-code directory> <code-pack manifest.txt>

A directory holds per-code packs `c<chart>/t<t>.pack` (
`pack5d --per_code`). Each is checked as its own table (row 0 is the job
root), skipping packs whose `.checked` file is newer, so a re-searched code
needs only its own check. When a pack passes, `<pack>.checked` is written:
bookkeeping for `scoreboard5d`, not part of any proof (the proof
is `constructPentagonalHexecontahedron`, which decodes the codes with `decodeCodeTables`).
-/

open Noperthedron.PentagonalHexecontahedron
open Noperthedron.PentagonalHexecontahedron.AtlasProjectiveSolutionTree

/-- Whether `a` was modified after `b` (both exist). -/
def newerThan (a b : System.FilePath) : IO Bool := do
  let ma := (← a.metadata).modified
  let mb := (← b.metadata).modified
  return ma.sec > mb.sec || (ma.sec == mb.sec && ma.nsec > mb.nsec)

/-- The rows of `table` in `[lo, hi)` that fail the row check. -/
def badRows (table : Table) (lo hi : Nat) : Array Nat := Id.run do
  let mut bad : Array Nat := #[]
  for i in [lo : hi] do
    unless validIxAtB table.chart table.get table.size table.sharedLocal i do
      bad := bad.push i
  bad

/-- Per-code directory: check each code's pack as its own table (row 0 is
the job root), skipping packs whose `.checked` file is newer, and write
`.checked` for each pack that passes. All codes' row chunks run as parallel
tasks. -/
def checkCodeDir (chart : CayleyAtlas.ChartIndex) (shared : SharedLocalTables)
    (dir : String) : IO UInt32 := do
  let chunk := 20000
  let mut jobs : Array (Nat × String × Table × Array (Task (Array Nat))) := #[]
  let mut skipped := 0
  for t in [0 : shared.size] do
    let path := s!"{dir}/c{chart.val}/t{t}.pack"
    let stamp := s!"{path}.checked"
    -- (Nested actions in `do` run before `&&`, so test existence first.)
    if ← System.FilePath.pathExists stamp then
      if ← newerThan stamp path then
        skipped := skipped + 1
        continue
    let table := PackedSolutionTree.decodeTable chart shared (← IO.FS.readFile path)
    let tasks := (List.range ((table.size + chunk - 1) / chunk)).toArray.map fun k =>
      Task.spawn fun _ => badRows table (k * chunk) (min table.size ((k + 1) * chunk))
    jobs := jobs.push (t, path, table, tasks)
  IO.println s!"{jobs.size} code packs to check ({skipped} already checked)"
  let mut failed := 0
  for (t, path, table, tasks) in jobs do
    let bad := tasks.foldl (fun acc task => acc ++ task.get) #[]
    if bad.isEmpty then
      IO.FS.writeFile s!"{path}.checked" s!"all {table.size} rows valid\n"
      IO.println s!"t={t}: all {table.size} rows valid"
    else
      failed := failed + 1
      IO.println s!"t={t}: {bad.size} invalid rows; first: {bad.toList.take 20}"
  IO.println (if failed == 0 then s!"all {jobs.size} code packs valid"
    else s!"{failed} code packs invalid")
  return (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  let (chartStr, packPath, manifestPath) ← match args with
    | [c, p, m] => pure (c, p, m)
    | _ => throw (IO.userError "usage: check_global_rows <chart> <pack> <code-pack manifest.txt>")
  let chart : CayleyAtlas.ChartIndex := ⟨chartStr.toNat! % 4, by omega⟩
  let packDir := (System.FilePath.mk manifestPath).parent.getD "."
  let mut shared : SharedLocalTables := #[]
  for line in ← IO.FS.lines manifestPath do
    if let filename :: _ := line.splitOn " " then
      if filename.endsWith ".pack" then
        let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
        shared := shared.push (PackedLocalViewTree.decodePackedCodeTriangle data)
  IO.println s!"{shared.size} identity-tube tables"
  if ← System.FilePath.isDir packPath then
    return ← checkCodeDir chart shared packPath
  let table := PackedSolutionTree.decodeTable chart shared (← IO.FS.readFile packPath)
  IO.println s!"{table.size} rows in {packPath}"
  let taskCount := 64
  let chunk := table.size / taskCount + 1
  let tasks := (List.range taskCount).map fun k =>
    Task.spawn fun _ => Id.run do
      let mut bad : Array Nat := #[]
      for i in [k * chunk : min table.size ((k + 1) * chunk)] do
        unless validIxAtB table.chart table.get table.size table.sharedLocal i do
          bad := bad.push i
      bad
  let mut bad : Array Nat := #[]
  for t in tasks do
    bad := bad ++ t.get
  if bad.isEmpty then
    IO.println s!"all {table.size} rows valid"
    IO.FS.writeFile s!"{packPath}.checked" s!"all {table.size} rows valid\n"
    return 0
  else
    IO.println s!"{bad.size} invalid rows; first: {bad.toList.take 20}"
    return 1
