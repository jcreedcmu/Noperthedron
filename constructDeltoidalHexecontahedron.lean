import Noperthedron.PentagonalHexecontahedron.FundamentalChart3
import Noperthedron.PentagonalHexecontahedron.DHDecode
import Noperthedron.PentagonalHexecontahedron.NativeExecutable
import Noperthedron.PentagonalHexecontahedron.PackedSolutionTree

/-!
Native executable that reads and checks the exact certificate data for the
deltoidal hexecontahedron, then constructs a proof that no deltoidal
hexecontahedron is Rupert.

Three kinds of data are decoded (untrusted) and checked natively, in parallel:
- the solution tables (packs, as for the pentagonal hexecontahedron), which
  exclude every centrally symmetric `IModel` whose exact claims hold;
- the three cap certificates (nopert229 `capcert --export`: u0, ux, u0 wide),
  which give the cap claims for the exact solid (`capsHold_of_certs`);
- the tie certificates (nopert229 `tietube --export_dir`, with `dh_tie_data.txt`
  and `nodes.txt`), which give the tie nodes' claims (`tiesHold_of_certs`).
Kernel-proved bridges (`check_of_par`, `tiesCheck_of_par`,
`deltoidalHexecontahedron_not_rupert_of_checks`) turn success into the theorem.
-/

open Noperthedron.PentagonalHexecontahedron
open Noperthedron.PentagonalHexecontahedron.AtlasProjectiveSolutionTree
open Noperthedron.PentagonalHexecontahedron.NativeExecutable
open Noperthedron.PentagonalHexecontahedron.Cap
open Noperthedron.PentagonalHexecontahedron.Tie
open Noperthedron.PentagonalHexecontahedron.DH
open Noperthedron.PentagonalHexecontahedron.DHDecode

private def localTaskCount : Nat := 64
private def globalTaskCount : Nat := 256

private def readArtifact (directory name : String) : IO String :=
  IO.FS.readFile s!"{directory}/{name}"

def main (args : List String) : IO Unit := do
  let (manifestPath, directory, capDir, tieDir) ← match args with
    | [m, d, c, t] => pure (m, d, c, t)
    | _ => throw (IO.userError (
        "usage: constructDeltoidalHexecontahedron <code-pack manifest.txt> <chart directory> " ++
        "<cap directory: u0.cert ux.cert u0_wide.cert> <tie directory: dh_tie_data.txt nodes.txt n*_t*.cert>"))
  -- Caps.
  let mut caps : Array CapCert := #[]
  for name in ["u0.cert", "ux.cert", "u0_wide.cert"] do
    caps := caps.push (decodeCert (← readLines s!"{capDir}/{name}"))
  IO.println s!"caps: {caps.map (·.charts.length)} charts"
  let capsStart ← IO.monoMsNow
  if hcaps : capsCheckPar caps = true then
    IO.println s!"valid caps: {(← IO.monoMsNow) - capsStart} ms"
    -- Ties.
    let mut certFiles : Array (ℕ × ℕ × Array String) := #[]
    for entry in ← System.FilePath.readDir tieDir do
      let name := entry.fileName
      if name.startsWith "n" && name.endsWith ".cert" then
        match (((name.drop 1).dropRight 5).toString).splitOn "_t" with
        | [n, tt] => certFiles := certFiles.push (n.toNat!, tt.toNat!, ← readLines entry.path.toString)
        | _ => pure ()
    let ties := decodeTies (← readLines s!"{tieDir}/dh_tie_data.txt") (← readLines s!"{tieDir}/nodes.txt") certFiles
    IO.println s!"ties: {ties.normals.size} normals, {certFiles.size} certificate files"
    let tiesStart ← IO.monoMsNow
    if hties : tiesCheckPar ties = true then
      IO.println s!"valid ties: {(← IO.monoMsNow) - tiesStart} ms"
      -- Tables (as for the pentagonal hexecontahedron).
      let packDir := (System.FilePath.mk manifestPath).parent.getD "."
      let mut localTables : SharedLocalTables := #[]
      for line in ← IO.FS.lines manifestPath do
        if let filename :: _ := line.splitOn " " then
          if filename.endsWith ".pack" then
            let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
            localTables := localTables.push (PackedLocalViewTree.decodePackedCodeTriangle data)
      let perCode ← System.FilePath.pathExists s!"{directory}/c0/t0.pack"
      let mut chartData : Array (Array String) := #[]
      for c in [0 : 3] do
        if perCode then
          let mut packs : Array String := #[]
          for tt in [0 : localTables.size] do
            packs := packs.push (← readArtifact directory s!"c{c}/t{tt}.pack")
          chartData := chartData.push packs
        else
          chartData := chartData.push #[← readArtifact directory s!"chart{c}.pack"]
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
      let _dh : ∀ V : Finset ℝ³, IsDeltoidalHexecontahedron V → ¬ IsRupert V :=
        deltoidalHexecontahedron_not_rupert_of_checks checked.down caps (capsCheck_of_par caps hcaps)
          ties (tiesCheck_of_par ties hties)
      IO.println "instantiated: no deltoidal hexecontahedron is Rupert"
    else
      throw (IO.userError "the tie certificates are not valid")
  else
    throw (IO.userError "the cap certificates are not valid")
