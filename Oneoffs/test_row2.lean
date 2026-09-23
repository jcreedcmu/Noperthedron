import Noperthedron.Nopert229.PackedSolutionTree
import Noperthedron.Nopert229.AtlasProjectiveGlobalCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree

def main : IO Unit := do
  let packPath := "/root/tom7misc/ruperts/test_cell_50.pack"
  let content ← IO.FS.readFile packPath
  let shared : SharedLocalTables := fun _ => none
  let table := PackedSolutionTree.decodeTable 0 shared content
  match table.get 7 with
  | .projectiveGlobal id box =>
    IO.println s!"Row 7: bernstein = {box.bernsteinDisplacementLower}"
  | _ => pure ()
