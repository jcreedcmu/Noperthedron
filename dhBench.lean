import Noperthedron.PentagonalHexecontahedron.DHDecode
import Noperthedron.PentagonalHexecontahedron.PackedLocalViewTree
import Noperthedron.PentagonalHexecontahedron.PackedSolutionTree

open Noperthedron.PentagonalHexecontahedron
open Noperthedron.PentagonalHexecontahedron.Cap
open Noperthedron.PentagonalHexecontahedron.DH
open Noperthedron.PentagonalHexecontahedron.DHDecode

instance : Inhabited Tie.TieNode := ⟨⟨0, fun _ _ => 0, 0, []⟩⟩
instance : Inhabited Tie.TieNormal := ⟨⟨fun _ => IcoQ.zero, #[], #[]⟩⟩

/-- Bench: `dhBench ties <dir>` or `dhBench cap <file>`. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["ties", tieDir] =>
    let mut certFiles : Array (ℕ × ℕ × Array String) := #[]
    for entry in ← System.FilePath.readDir tieDir do
      let name := entry.fileName
      if name.startsWith "n" && name.endsWith ".cert" then
        match (((name.drop 1).dropRight 5).toString).splitOn "_t" with
        | [n, tt] => certFiles := certFiles.push (n.toNat!, tt.toNat!, ← readLines entry.path.toString)
        | _ => pure ()
    let ties := decodeTies (← readLines s!"{tieDir}/dh_tie_data.txt") (← readLines s!"{tieDir}/nodes.txt") certFiles
    IO.println s!"ties: {ties.V.size} vertices, {ties.normals.size} normals, {ties.leaves.size} nodes, {certFiles.size} files"
    let t0 ← IO.monoMsNow
    IO.println s!"sameSlots: {sameSlots ties.V.toList}"
    -- Per-node diagnosis (sequential over failing nodes).
    let n := Tie.dhTieNodes.size
    let tasks := (List.range n).map fun k => Task.spawn fun _ => (k, nodePred ties k)
    let mut bad := 0
    for task in tasks do
      let (k, ok) := task.get
      if !ok then
        bad := bad + 1
        if bad ≤ 6 then
          let e := Tie.dhTieNodes[k]!
          match e.kids with
          | [] =>
            let N := ties.normals[e.normal]!
            let trees := ties.leaves[k]!
            let fc := (Tie.faces.zip trees).map fun fe => Tie.faceCheck N ties.V e.tri e.rho fe.1.1 fe.1.2 fe.2
            IO.println s!"leaf {k}: normal {e.normal} rho {e.rho} trees {trees.length} keq {keq N.x (AtlasTiePrune.tieXK e.normal)} lCheck {Tie.lCheck N ties.V} faces {fc}"
          | kids => IO.println s!"split {k}: kids {kids}"
    IO.println s!"{bad} failing nodes ({(← IO.monoMsNow) - t0} ms)"
  | ["cap", file] =>
    let c := decodeCert (← readLines file)
    let t0 ← IO.monoMsNow
    IO.println s!"{c.charts.length} charts; capCheckPar: {capCheckPar c} ({(← IO.monoMsNow) - t0} ms)"
  | "rows" :: chartStr :: packPath :: manifestPath :: idx =>
    let chart : CayleyAtlas.ChartIndex := ⟨chartStr.toNat! % 4, by omega⟩
    let packDir := (System.FilePath.mk manifestPath).parent.getD "."
    let mut shared : AtlasProjectiveSolutionTree.SharedLocalTables := #[]
    for line in ← IO.FS.lines manifestPath do
      if let filename :: _ := line.splitOn " " then
        if filename.endsWith ".pack" then
          shared := shared.push (PackedLocalViewTree.decodePackedCodeTriangle (← IO.FS.readBinFile s!"{packDir}/{filename}"))
    let table := PackedSolutionTree.decodeTable chart shared (← IO.FS.readFile packPath)
    for s in idx do
      let i := s.toNat!
      let row := table.get i
      let kind : String := match row with
        | .tieLeaf _ box root node =>
          s!"tieLeaf normal {box.normal} rho {box.rho} node {node} root {root} chart {box.chart}: boxValid {decide box.Valid} nodeOk {AtlasProjectiveSolutionTree.tieLeafValidB box node}"
        | .capLeaf _ iv root tri cap => s!"capLeaf cap {cap} root {root}: valid {AtlasProjectiveSolutionTree.capLeafValidB iv tri cap}"
        | .halfTurnPrune _ box root => s!"halfTurnPrune g {box.element} root {root}: valid {decide box.Valid}"
        | .symmetryTube _ tube si path _ => s!"symmetryTube shared {si} path {path.length} r {tube.r}"
        | .regionRelax .. => "regionRelax"
        | .cayleySplit .. => "cayleySplit" | .cayleySplitAt .. => "cayleySplitAt"
        | .viewSplit .. => "viewSplit" | .viewRoot .. => "viewRoot" | .codeRoot .. => "codeRoot"
        | .projective .. => "projective" | .projectiveGlobal .. => "projectiveGlobal"
        | .projectiveMixedGlobal .. => "mixedGlobal" | .symmetryLocal .. => "symmetryLocal"
        | .projectiveLocal .. => "projectiveLocal" | .radiusPrune .. => "radiusPrune"
        | .fundamentalPrune .. => "fundamentalPrune" | .icoPrune .. => "icoPrune"
      IO.println s!"row {i} (id {row.id}): {kind}"
  | _ => IO.println "usage: dhBench ties <dir> | cap <file> | rows <chart> <pack> <manifest> <i>..."
