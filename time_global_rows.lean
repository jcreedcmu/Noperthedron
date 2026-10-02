import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.PackedSolutionTree

/-!
Single-threaded timing of Lean's row checker (`validIxAtB`) on a 5D search
pack, by row kind: where does checking time go?

Usage: time_global_rows <chart> <pack> <code-pack manifest.txt>
-/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree

def rowKind : Row → String
  | .cayleySplit .. => "cayleySplit"
  | .viewRoot .. => "viewRoot"
  | .viewSplit .. => "viewSplit"
  | .projective .. => "projective"
  | .projectiveGlobal .. => "projectiveGlobal"
  | .projectiveMixedGlobal .. => "projectiveMixedGlobal"
  | .symmetryLocal .. => "symmetryLocal"
  | .projectiveLocal .. => "projectiveLocal"
  | .symmetryTube .. => "symmetryTube"
  | .codeRoot .. => "codeRoot"
  | .radiusPrune .. => "radiusPrune"
  | .fundamentalPrune .. => "fundamentalPrune"
  | .regionRelax .. => "regionRelax"
  | .cayleySplitAt .. => "cayleySplitAt"

def main (args : List String) : IO UInt32 := do
  let (chartStr, packPath, manifestPath) ← match args with
    | [c, p, m] => pure (c, p, m)
    | _ => throw (IO.userError "usage: time_global_rows <chart> <pack> <code-pack manifest.txt>")
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
  let mut stats : Std.HashMap String (Nat × Nat) := {}
  let mut bad := 0
  for i in [0 : table.size] do
    let kind := rowKind (table.get i)
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => validIxAtB table.chart table.get table.size table.sharedLocal i
    let t1 ← IO.monoNanosNow
    unless ok do bad := bad + 1
    let (n, ns) := stats.getD kind (0, 0)
    stats := stats.insert kind (n + 1, ns + (t1 - t0))
  for (kind, (n, ns)) in stats.toList do
    IO.println s!"{kind}: {n} rows, {ns / 1000000} ms, {ns / n / 1000} us/row"
  IO.println s!"{bad} invalid rows"
  return if bad == 0 then 0 else 1
