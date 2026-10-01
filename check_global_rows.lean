import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.PackedSolutionTree

/-!
Development checker for 5D search packs (nopert229/pack5d): decodes a
global pack for one chart, with the identity-tube code tables as shared
tables, and checks every row with Lean's row checker
(`AtlasProjectiveSolutionTree.validIxAtB`), reporting the rows that fail.

Unlike `constructNopert229`, this works for partial packs (e.g. one job's
tree with its root node as row 0), which are not valid chart tables.

Usage: check_global_rows <chart> <pack> <code-pack manifest.txt>
-/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree

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
  let packed ← IO.FS.readFile packPath
  let table := PackedSolutionTree.decodeTable chart shared packed
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
    return 0
  else
    IO.println s!"{bad.size} invalid rows; first: {bad.toList.take 20}"
    return 1
