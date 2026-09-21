import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
import Noperthedron.Nopert229.AtlasProjectiveView

open Noperthedron.Nopert229
open Noperthedron.Nopert229.PackedLocalViewTree
open AtlasProjectiveView AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

/-- Decomposed leaf row data representing an annular / inner core / complement certificate. -/
structure DecomposedLeafData where
  id : Nat
  root : Fin 8
  triangle : AtlasProjectiveView.Triangle Rat
  path : List (Fin 4)
  symmetryIndex : Fin 5
  r_min : Rat
  r : Rat
  c : Rat
  delta : Rat
  innerIndices : Fin 3 → VertexIndex
  innerCoreAxis : AxisCertificate
  complementAxes : Array AxisCertificate

def readDecomposedRow (base : AtlasProjectiveView.Triangle Rat) : Decoder DecomposedLeafData := do
  let tag ← readNat
  unless tag = 2 do
    panic! s!"Expected tag 2 for decomposed leaf row, got {tag}"
  let id ← readNat
  let root ← readNat
  let length ← readNat
  let mut pt := PrecomputedTriangle.ofTriangle base
  let mut pathList : List (Fin 4) := []
  for _ in [0:length] do
    let d ← readNat
    let f := fin4 d
    pathList := pathList ++ [f]
    pt := stepTriangle pt f
  let triangle := pt.toTriangle
  let symmetryIndex ← readNat
  let r_min ← readRat
  let r ← readRat
  let c ← readRat
  let delta ← readRat
  let i0 ← readNat
  let i1 ← readNat
  let i2 ← readNat
  let innerIndices : Fin 3 → VertexIndex := ![fin20 i0, fin20 i1, fin20 i2]
  let innerCoreAxis ← readAxis
  let numComp ← readNat
  let mut compAxes : Array AxisCertificate := #[]
  for _ in [0:numComp] do
    let ax ← readAxis
    compAxes := compAxes.push ax
  pure {
    id
    root := fin8 root
    triangle
    path := pathList
    symmetryIndex := fin5 symmetryIndex
    r_min
    r
    c
    delta
    innerIndices
    innerCoreAxis
    complementAxes := compAxes
  }

def decodeDecomposedPack (base : AtlasProjectiveView.Triangle Rat) (packed : String) :
    DecomposedLeafData :=
  (do
    let _count ← readNat
    let _sym ← readNat
    let _table_r ← readRat
    readDecomposedRow base
  ).run { data := packed.toUTF8 } |>.1

def main : IO Unit := do
  let packPath : System.FilePath := "/home/tom/nopert-project/ruperts/decomposed_leaf.pack"
  let content ← IO.FS.readFile packPath
  IO.println s!"Read {content.length} characters from {packPath}."

  let base := split upperWedgeTriangle 0
  let leaf := decodeDecomposedPack base content

  IO.println s!"Decoded Leaf ID: {leaf.id}"
  IO.println s!"Path length: {leaf.path.length}"
  IO.println s!"r_min: {leaf.r_min}, r: {leaf.r}, c: {leaf.c}, delta: {leaf.delta}"
  IO.println s!"Inner indices: {[leaf.innerIndices 0, leaf.innerIndices 1, leaf.innerIndices 2]}"
  IO.println s!"Inner core B: {leaf.innerCoreAxis.B}"
  IO.println s!"Complement axes count: {leaf.complementAxes.size}"

  -- Verification step 1: Check r_min and r ordering
  if leaf.r_min ≤ 0 || leaf.r ≤ leaf.r_min then
    throw (IO.userError "FAIL: invalid radii ordering")

  -- Verification step 2: Check inner core contacts
  let core := leaf.innerCoreAxis
  if core.B ≤ 0 then
    throw (IO.userError "FAIL: inner core B <= 0")

  -- Verification step 3: Check complement axes count
  if leaf.complementAxes.size < 3 then
    throw (IO.userError "FAIL: fewer than 3 complement axes")

  let box_core : Box := {
    interval := AtlasPose.rootInterval Rat
    root := leaf.root
    triangle := leaf.triangle
    chart := 0
    symmetryIndex := leaf.symmetryIndex
    certificate := fun _ => leaf.innerCoreAxis
    c := leaf.c
    δ := leaf.delta
    r := leaf.r
  }

  for i in [0:3] do
    for k in [0:20] do
      let sup := box_core.supportUpper 0 (fin3 i) (fin20 k)
      if sup > 0 then
        throw (IO.userError s!"FAIL: inner core support defect > 0: {sup} at i={i}, k={k}")

  IO.println "All 60 inner core support bounds strictly <= 0 verified on decoded triangle!"

  for ax in leaf.complementAxes do
    let box_comp : Box := {
      interval := AtlasPose.rootInterval Rat
      root := leaf.root
      triangle := leaf.triangle
      chart := 0
      symmetryIndex := leaf.symmetryIndex
      certificate := fun _ => ax
      c := leaf.c
      δ := leaf.delta
      r := leaf.r
    }
    for i in [0:3] do
      for k in [0:20] do
        let sup := box_comp.supportUpper 0 (fin3 i) (fin20 k)
        if sup > 0 then
          throw (IO.userError s!"FAIL: complement axis support defect > 0: {sup} at i={i}, k={k}")

  IO.println s!"All {leaf.complementAxes.size * 60} complement axes support bounds strictly <= 0 verified on decoded triangle!"
  IO.println "=== DECOMPOSED CERTIFICATE PACKED VERIFICATION SUCCESSFUL! ==="
