import Noperthedron.Nopert229.FundamentalChart3
import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedSolutionTree

/-!
Native executable that reads and checks exact certificate data, then constructs
a proof that the fivefold-symmetric polyhedron (Nopert #231 on this branch) is not Rupert.

This is analogous to `constructValidTable`: the expensive Boolean checks run
as parallel native code, while kernel-proved bridge theorems turn success into
the semantic proof consumed by the public theorem.
-/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree
open Noperthedron.Nopert229.NativeExecutable

/-- A completed local-table audit found 64 chunks materially faster than 512
for these comparatively expensive exact-rational rows. -/
private def localTaskCount : Nat := 64

/-- Global tables are much larger, and chart 0's expensive projective-local
leaves occupy relatively few contiguous ranges.  Finer chunks improve tail
load balancing without imposing the local checker's tiny-chunk overhead. -/
private def globalTaskCount : Nat := 256

private def readArtifact (directory name : String) : IO String :=
  IO.FS.readFile s!"{directory}/{name}"

def main (args : List String) : IO Unit := do
  let (manifestPath, directory) ← match args with
    | [m, d] => pure (m, d)
    | _ => throw (IO.userError (
        "usage: constructNopert229 <code-pack manifest.txt> <chart directory>; " ++
        "the manifest lists the identity-tube code packs in code order, and the " ++
        "directory holds chart0.pack through chart2.pack"))
  let packDir := (System.FilePath.mk manifestPath).parent.getD "."
  let mut localTables : SharedLocalTables := #[]
  for line in ← IO.FS.lines manifestPath do
    if let filename :: _ := line.splitOn " " then
      if filename.endsWith ".pack" then
        let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
        localTables := localTables.push (PackedLocalViewTree.decodePackedCodeTriangle data)
  let chart0Data ← readArtifact directory "chart0.pack"
  let chart1Data ← readArtifact directory "chart1.pack"
  let chart2Data ← readArtifact directory "chart2.pack"
  let globalTables : SharedLocalTables →
      CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table :=
    fun shared =>
      ![PackedSolutionTree.decodeTable 0 shared chart0Data,
        PackedSolutionTree.decodeTable 1 shared chart1Data,
        PackedSolutionTree.decodeTable 2 shared chart2Data,
        { FundamentalChart3.table with sharedLocal := shared }]
  let checked ← constructProof localTaskCount globalTaskCount
    localTables globalTables
    (by intro shared chart; fin_cases chart <;> rfl)
    (by intro shared chart; fin_cases chart <;> rfl)
  let _proof : ¬ IsRupert exactVerts := checked.down
