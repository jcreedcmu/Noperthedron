import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree

/-! Time single-threaded row checks on a strided sample of a code pack.
Usage: time_pack_rows <file.pack> <samples> -/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.SparseLocalViewTree

def main (args : List String) : IO Unit := do
  let path := args[0]!
  let samples := (args[1]!).toNat!
  let table := PackedLocalViewTree.decodePackedCodeTriangle (← IO.FS.readBinFile path)
  let stride := max 1 (table.size / samples)
  let start ← IO.monoNanosNow
  let mut n := 0
  let mut i := 0
  while i < table.size do
    let ok := sparseChunkValidB table.symmetryIndex table.r table.get table.size i 1
    unless ok do IO.println s!"row {i} INVALID"
    n := n + 1
    let el := ((← IO.monoNanosNow) - start) / 1000000
    IO.println s!"row {i}: cumulative {el} ms over {n} rows ({el / n} ms/row)"
    (← IO.getStdout).flush
    i := i + stride
  let ms := ((← IO.monoNanosNow) - start) / 1000000
  IO.println s!"{path}: {table.size} rows; checked {n} sampled rows in {ms} ms = {ms / n} ms/row; est. {table.size * ms / n / 1000 / 16} s on 16 cores"
