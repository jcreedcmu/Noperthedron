import Noperthedron.Nopert229.PackedSolutionTree
import Noperthedron.Nopert229.AtlasProjectiveMixedGlobalCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree
open Noperthedron.Nopert229.AtlasProjectiveMixedGlobalCertificate

def main : IO Unit := do
  let packPath := "/root/tom7misc/ruperts/test_cell_50.pack"
  let content ← IO.FS.readFile packPath
  let shared : SharedLocalTables := fun _ => none
  let table := PackedSolutionTree.decodeTable 0 shared content
  IO.println s!"Total rows in table: {table.size}"

  let mut mixedIndices : List Nat := []
  for i in [0:table.size] do
    match table.get i with
    | .projectiveMixedGlobal .. =>
      mixedIndices := i :: mixedIndices
    | _ => pure ()

  mixedIndices := mixedIndices.reverse
  IO.println s!"Found {mixedIndices.length} mixed-global rows."

  let mut pass := 0
  let mut fail := 0
  let mut failingList : List (Nat × ℚ) := []

  let start ← IO.monoNanosNow
  for i in mixedIndices do
    let r := table.get i
    match r with
    | .projectiveMixedGlobal id box =>
      let valid := validIxAtB table.chart table.get table.size table.sharedLocal i
      if valid then
        pass := pass + 1
      else
        fail := fail + 1
        let bLower := box.bernsteinDisplacementLower
        let penalty := box.dBound * box.weightedDefectUpper
        let err := box.displacementError
        let margin := bLower - penalty - err
        failingList := (i, margin) :: failingList
        IO.println s!"FAIL ix={i} id={id} margin={margin}"
        IO.println s!"  weights: w0={box.weight 0} w1={box.weight 1} w2={box.weight 2} w3={box.weight 3}"
        IO.println s!"  bLower={bLower} penalty={penalty} err={err}"
    | _ => pure ()

  let finish ← IO.monoNanosNow
  let elapsedMs := (finish - start) / 1000000
  IO.println s!"Done in {elapsedMs} ms! Pass: {pass}, Fail: {fail}"
