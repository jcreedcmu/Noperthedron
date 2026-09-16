import Noperthedron.Nopert229.PackedSolutionTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree

def main : IO Unit := do
  let packPath := "/home/tom/ruperts-head/test_mx.pack"
  let content ← IO.FS.readFile packPath
  let shared : SharedLocalTables := fun _ => none
  let table := PackedSolutionTree.decodeTable 0 shared content
  IO.println s!"Table decoded successfully! Size = {table.size}"
  let r := table.get 2
  match r with
  | .projectiveMixedGlobal id _ =>
    IO.println s!"Row 2 is projectiveMixedGlobal with id {id}"
    let valid := validIxAtB table.chart table.get table.size table.sharedLocal 2
    IO.println s!"validIxAtB for row 2: {valid}"
    if valid then
      IO.println "TEST PASSED: Mixed Global packed row decoded and validated!"
    else
      throw (IO.userError "TEST FAILED: validIxAtB returned false!")
  | _ =>
    throw (IO.userError "TEST FAILED: Row 2 was not projectiveMixedGlobal!")
