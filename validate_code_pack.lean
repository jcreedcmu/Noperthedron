import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.NativeExecutable

private def taskCount : Nat := 8

def validateFile (path : String) : IO Unit := do
  let data ← IO.FS.readBinFile path
  let table := PackedLocalViewTree.decodePackedCodeTriangle data
  let firstId := (table.get 0).id
  unless firstId = 0 do
    throw (IO.userError s!"{path}: packed table has an invalid first row id {firstId}")
  let checked ← checkLocal path taskCount table
  let _semanticProof : table.Valid := checked.down
  IO.println s!"[LEAN VALIDATED] {path} | rows: {table.size} | r: {table.r} -> table.Valid PROVED"

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
    throw (IO.userError "Usage: validate_code_pack <file.pack ...> or validate_code_pack --manifest <manifest.txt>")
  | ["--manifest", manifestPath] =>
    let lines ← IO.FS.lines manifestPath
    let dir := (System.FilePath.mk manifestPath).parent.getD "."
    let mut totalRows := 0
    let mut count := 0
    for line in lines do
      let parts := line.splitOn " "
      if let filename :: _ := parts then
        if filename.endsWith ".pack" then
          let packPath := s!"{dir}/{filename}"
          validateFile packPath
          count := count + 1
    IO.println s!"\n=== ALL {count} PACKED TABLES VALIDATED IN LEAN (table.Valid with NO sorry) ==="
  | paths =>
    for path in paths do
      validateFile path
