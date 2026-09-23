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
  let r := table.get 10073
  match r with
  | .projectiveMixedGlobal id box =>
    IO.println s!"Testing weights on row 10073..."
    -- Let w0 vary from 40/100 to 50/100
    for num in [420:450] do
      let w0 : ℚ := (num : ℚ) / 1000
      let w1 : ℚ := 1 - w0
      let testBox : AtlasProjectiveMixedGlobalCertificate.Box := {
        box with
        weight := ![w0, w1, 0, 0]
      }
      let bLower := testBox.bernsteinDisplacementLower
      let penalty := testBox.dBound * testBox.weightedDefectUpper
      let err := testBox.displacementError
      let margin := bLower - penalty - err
      if margin > 0 then
        IO.println s!"FOUND POSITIVE MARGIN: w0={w0} w1={w1} margin={margin}"
        IO.println s!"Valid: {decide testBox.Valid}"
  | _ => pure ()
