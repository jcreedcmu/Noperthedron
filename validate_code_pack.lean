import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.NativeExecutable

private def taskCount : Nat := 16

def validateFile (path : String) (force : Bool := false) : IO Unit := do
  let stampPath := s!"{path}.validated"
  let data ← IO.FS.readBinFile path
  if !force then
    if ← System.FilePath.pathExists stampPath then
      let stampContent ← IO.FS.readFile stampPath
      if stampContent.containsSubstr "status: table.Valid PROVED" then
        IO.println s!"[LEAN CACHED] {path} -> table.Valid already verified ({stampPath})"
        return ()
  let table := PackedLocalViewTree.decodePackedCodeTriangle data
  let firstId := (table.get 0).id
  unless firstId = 0 do
    throw (IO.userError s!"{path}: packed table has an invalid first row id {firstId}")
  let checked ← checkLocal path taskCount table
  let _semanticProof : table.Valid := checked.down
  let stampText := s!"# Nopert #229 Lean 4 Validation Witness\nfile: {(System.FilePath.mk path).fileName.getD path}\nsize_bytes: {data.size}\nrows: {table.size}\nr: {table.r}\nstatus: table.Valid PROVED\n"
  IO.FS.writeFile stampPath stampText
  IO.println s!"[LEAN VALIDATED] {path} | rows: {table.size} | r: {table.r} -> table.Valid PROVED (wrote {stampPath})"

def main (args : List String) : IO Unit := do
  let force := args.contains "--force"
  let cleanArgs := args.filter (· != "--force")
  match cleanArgs with
  | [] =>
    throw (IO.userError "Usage: validate_code_pack [--force] <file.pack ...> or validate_code_pack [--force] --manifest <manifest.txt>")
  | ["--manifest", manifestPath] =>
    let lines ← IO.FS.lines manifestPath
    let dir := (System.FilePath.mk manifestPath).parent.getD "."
    let mut count := 0
    for line in lines do
      let parts := line.splitOn " "
      if let filename :: _ := parts then
        if filename.endsWith ".pack" then
          let packPath := s!"{dir}/{filename}"
          validateFile packPath force
          count := count + 1
    IO.println s!"\n=== ALL {count} PACKED TABLES PROCESSED IN LEAN ==="
  | paths =>
    for path in paths do
      validateFile path force
