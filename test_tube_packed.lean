import Noperthedron.Nopert229.PackedSolutionTree
import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.PackedLocalViewTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree
open Noperthedron.Nopert229.PackedLocalViewTree

def dummyTable0 : AtlasProjectiveLocalViewTree.Table where
  symmetryIndex := 0
  r := 1 / 10
  root := 0
  triangle := Noperthedron.SnubCube.ProjectiveView.split AtlasProjectiveView.upperWedgeTriangle 0
  get := fun _ => .split 0 (fun _ => 0) 0 (Noperthedron.SnubCube.ProjectiveView.split AtlasProjectiveView.upperWedgeTriangle 0)
  size := 1

def main : IO Unit := do
  -- Test 1: Unit tests for Table.findNode navigation
  IO.println "=== Test 1: Unit tests for Table.findNode ==="
  let tri0 := Noperthedron.SnubCube.ProjectiveView.split AtlasProjectiveView.upperWedgeTriangle 0
  let tri00 := Noperthedron.SnubCube.ProjectiveView.split tri0 0
  -- Multi-level test tree:
  -- Node 0: split -> children [1, 2, 3, 4]
  -- Node 1: split -> children [5, 6, 7, 8]
  let testTable : AtlasProjectiveLocalViewTree.Table := {
    symmetryIndex := 0
    r := 1 / 10
    root := 0
    triangle := tri0
    get := fun i =>
      if i = 0 then .split 0 (fun c => c.val + 1) 0 tri0
      else if i = 1 then .split 1 (fun c => c.val + 5) 0 tri00
      else .split i (fun _ => 0) 0 tri0
    size := 9
  }
  -- Path [] should find root (node 0)
  if testTable.findNode [] != some 0 then
    throw (IO.userError "FAIL: findNode [] did not return some 0")
  -- Path [0] should find node 1
  if testTable.findNode [0] != some 1 then
    throw (IO.userError "FAIL: findNode [0] did not return some 1")
  -- Path [1] should find node 2
  if testTable.findNode [1] != some 2 then
    throw (IO.userError "FAIL: findNode [1] did not return some 2")
  -- Path [0, 0] should find node 5
  if testTable.findNode [0, 0] != some 5 then
    throw (IO.userError "FAIL: findNode [0, 0] did not return some 5")
  -- Path [0, 1] should find node 6
  if testTable.findNode [0, 1] != some 6 then
    throw (IO.userError "FAIL: findNode [0, 1] did not return some 6")
  IO.println "findNode unit tests passed!"

  -- Test 2: Verify real production atlas local-view3.pack
  IO.println "=== Test 2: Real atlas navigation (local-view3.pack) ==="
  let lv3Path : System.FilePath := "local-view3.pack"
  if ← lv3Path.pathExists then
    let lv3Data ← IO.FS.readFile lv3Path
    let lv3Table := PackedLocalViewTree.decodePackedTable 3 lv3Data
    IO.println s!"Loaded local-view3.pack: size = {lv3Table.size}, r = {lv3Table.r}"
    if lv3Table.findNode [] != some 0 then
      throw (IO.userError "FAIL: lv3Table findNode [] != some 0")
    let rootNode := lv3Table.get 0
    match rootNode with
    | .split _ children _ _ =>
      IO.println s!"Root node 0 is split with children {[children 0, children 1, children 2, children 3]}"
      -- Verify navigating to each child
      for c in [0, 1, 2, 3] do
        let cid := children (fin4 c)
        let found := lv3Table.findNode [fin4 c]
        if found != some cid then
          throw (IO.userError s!"FAIL: findNode [{c}] returned {found}, expected {some cid}")
      IO.println "Subdivision step navigation verified on local-view3.pack!"
    | _ => throw (IO.userError "Expected root of local-view3 to be .split")

  -- Test 3: Decode and validate symmetryTube from chart0.pack
  IO.println "=== Test 3: Validate symmetryTube rows in chart0.pack ==="
  let packPath := "/home/tom/ruperts-head/test_tube_run/chart0.pack"
  let content ← IO.FS.readFile packPath
  IO.println s!"Read {content.length} bytes from {packPath}"
  let shared : SharedLocalTables := fun i => if i.val = 0 then some dummyTable0 else none
  let table := PackedSolutionTree.decodeTable 0 shared content
  IO.println s!"Table decoded successfully! Size = {table.size}"
  for rowId in [7055, 7057, 7059, 7061] do
    let r := table.get rowId
    match r with
    | .symmetryTube id tube sharedIndex path _ =>
      IO.println s!"Row {rowId} is symmetryTube!"
      IO.println s!"  id: {id}, tube.chart: {tube.chart}, tube.r: {tube.r}, sharedIndex: {sharedIndex}, path: {path}"
      let valid := validIxAtB table.chart table.get table.size table.sharedLocal rowId
      IO.println s!"  validIxAtB: {valid}"
      if !valid then
        throw (IO.userError s!"TEST FAILED: validIxAtB returned false for row {rowId}!")
    | _ =>
      throw (IO.userError s!"TEST FAILED: Row {rowId} was not symmetryTube!")

  -- Test 4: Negative test - if shared local table does NOT match path
  IO.println "=== Test 4: Negative test ==="
  let emptyShared : SharedLocalTables := fun _ => none
  let tableEmpty := PackedSolutionTree.decodeTable 0 emptyShared content
  let validEmpty := validIxAtB tableEmpty.chart tableEmpty.get tableEmpty.size tableEmpty.sharedLocal 7055
  IO.println s!"  validIxAtB with emptyShared (expected false): {validEmpty}"
  if validEmpty then
    throw (IO.userError "TEST FAILED: validIxAtB should be false when sharedLocal is none!")

  IO.println "ALL TESTS PASSED: length+digits hierarchical tube path successfully implemented and validated!"
