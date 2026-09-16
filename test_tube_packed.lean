import Noperthedron.Nopert229.PackedSolutionTree
import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree

def dummyTable0 : AtlasProjectiveLocalViewTree.Table where
  symmetryIndex := 0
  r := 1 / 10
  root := 0
  triangle := Noperthedron.SnubCube.ProjectiveView.split AtlasProjectiveView.upperWedgeTriangle 0
  get := fun _ => .split 0 (fun _ => 0) 0 (Noperthedron.SnubCube.ProjectiveView.split AtlasProjectiveView.upperWedgeTriangle 0)
  size := 1

def main : IO Unit := do
  let packPath := "/home/tom/ruperts-head/test_tube_run/chart0.pack"
  let content ← IO.FS.readFile packPath
  IO.println s!"Read {content.length} bytes from {packPath}"
  let shared : SharedLocalTables := fun i => if i.val = 0 then some dummyTable0 else none
  let table := PackedSolutionTree.decodeTable 0 shared content
  IO.println s!"Table decoded successfully! Size = {table.size}"
  for rowId in [7055, 7057, 7059, 7061] do
    let r := table.get rowId
    match r with
    | .symmetryTube id tube sharedIndex nodeId region =>
      IO.println s!"Row {rowId} is symmetryTube!"
      IO.println s!"  id: {id}, tube.chart: {tube.chart}, tube.r: {tube.r}, sharedIndex: {sharedIndex}, nodeId: {nodeId}"
      let valid := validIxAtB table.chart table.get table.size table.sharedLocal rowId
      IO.println s!"  validIxAtB: {valid}"
      if !valid then
        throw (IO.userError s!"TEST FAILED: validIxAtB returned false for row {rowId}!")
    | _ =>
      throw (IO.userError s!"TEST FAILED: Row {rowId} was not symmetryTube!")
  IO.println "TEST PASSED: all symmetryTube rows decoded and validated successfully!"
