import Noperthedron.Nopert229.FundamentalChart3
import Noperthedron.Nopert229.Ideal231
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
        "directory holds chart0.pack through chart2.pack, or per-code packs " ++
        "c<chart>/t<t>.pack (nopert229 pack5d --per_code)"))
  let packDir := (System.FilePath.mk manifestPath).parent.getD "."
  let mut localTables : SharedLocalTables := #[]
  for line in ← IO.FS.lines manifestPath do
    if let filename :: _ := line.splitOn " " then
      if filename.endsWith ".pack" then
        let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
        localTables := localTables.push (PackedLocalViewTree.decodePackedCodeTriangle data)
  -- Chart data: one pack per chart, or one per code triangle (decoded and
  -- concatenated behind a codeRoot row; decoding is untrusted either way).
  let perCode ← System.FilePath.pathExists s!"{directory}/c0/t0.pack"
  let mut chartData : Array (Array String) := #[]
  for c in [0 : 3] do
    if perCode then
      let mut packs : Array String := #[]
      for t in [0 : localTables.size] do
        packs := packs.push (← readArtifact directory s!"c{c}/t{t}.pack")
      chartData := chartData.push packs
    else
      chartData := chartData.push #[← readArtifact directory s!"chart{c}.pack"]
  IO.println s!"chart data: {if perCode then "per-code packs" else "one pack per chart"}"
  let decode (chart : CayleyAtlas.ChartIndex) (shared : SharedLocalTables)
      (data : Array String) : AtlasProjectiveSolutionTree.Table :=
    let table := if perCode then PackedSolutionTree.decodeCodeTables chart shared data
      else PackedSolutionTree.decodeTable chart shared data[0]!
    { table with chart, sharedLocal := shared }
  let globalTables : SharedLocalTables →
      CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table :=
    fun shared =>
      ![decode 0 shared chartData[0]!,
        decode 1 shared chartData[1]!,
        decode 2 shared chartData[2]!,
        { FundamentalChart3.table with sharedLocal := shared }]
  let checked ← constructProof localTaskCount globalTaskCount
    localTables globalTables
    (by intro shared chart; fin_cases chart <;> rfl)
    (by intro shared chart; fin_cases chart <;> rfl)
  let proof : ∀ P : C5Model, ¬ IsRupert P.verts := checked.down
  -- The verified model (exact rotations of the rational seeds) and idealized
  -- #231 (exactly planar quads, `Ideal231.quad_planar`).
  let _exact : ¬ IsRupert exactVerts := exactModel_verts ▸ proof exactModel
  let _ideal : ¬ IsRupert Ideal231.model.verts := proof Ideal231.model
  IO.println "instantiated: the exact model (exactVerts) and idealized #231 are not Rupert"
