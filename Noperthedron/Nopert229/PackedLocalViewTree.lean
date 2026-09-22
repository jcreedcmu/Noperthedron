module

public import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree

@[expose] public section

/-!
# Packed native certificates for the Nopert #229 local view tree

Large generated local certificates contain very little repeated axis data.
Representing every integer in that data as a separate Lean declaration makes
elaboration and code generation dominate the actual certificate check.  This
module provides a deliberately small total decoder for comma-separated natural
numbers.  Generated native-only modules can therefore contain one string
literal; `native_decide` still checks the fully decoded exact rational table.

Signed rational numerators use zig-zag coding: `z >= 0` is encoded as `2*z`,
and `z < 0` as `-2*z-1`.
-/

namespace Noperthedron.Nopert229.PackedLocalViewTree

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open AtlasProjectiveLocalViewTree
open Noperthedron.SnubCube.ProjectiveView

structure Cursor where
  data : ByteArray
  pos : Nat := 0

def Cursor.readNat (cursor : Cursor) : Nat × Cursor :=
  Id.run do
    let data := cursor.data
    let mut pos := cursor.pos
    let mut acc : Nat := 0
    let size := data.size
    while h : pos < size do
      let byte := data[pos]
      pos := pos + 1
      if byte = 44 then
        break
      let value := byte.toNat
      if 48 ≤ value ∧ value ≤ 57 then
        acc := 10 * acc + value - 48
    (acc, { cursor with pos })


abbrev Decoder := StateM Cursor

def readNat : Decoder Nat := fun cursor => cursor.readNat

def fin3 (n : Nat) : Fin 3 := ⟨n % 3, by omega⟩
def fin4 (n : Nat) : Fin 4 := ⟨n % 4, by omega⟩
def fin5 (n : Nat) : Fin 5 := ⟨n % 5, by omega⟩
def fin8 (n : Nat) : Fin 8 := ⟨n % 8, by omega⟩
def fin20 (n : Nat) : Fin 20 := ⟨n % 20, by omega⟩
def fin1001 (n : Nat) : Fin 1001 := ⟨n % 1001, by omega⟩

def zigzagInt (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

def readRat : Decoder Rat := do
  let numerator ← readNat
  let denominator ← readNat
  pure ((((zigzagInt numerator : Int) : Rat) / (denominator : Rat)) : Rat)

def readVertices : Decoder (Fin 3 → VertexIndex) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![fin20 a, fin20 b, fin20 c]

def readMix : Decoder (Fin 3 → Fin 1001) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![fin1001 a, fin1001 b, fin1001 c]

def readAxis : Decoder AxisCertificate := do
  let edgeStart ← readVertices
  let edgeFinish ← readVertices
  let edgeStart₂ ← readVertices
  let edgeFinish₂ ← readVertices
  let mix ← readMix
  let index ← readVertices
  let nonzeroWitness ← readVertices
  let B ← readRat
  pure {
    edgeStart := edgeStart
    edgeFinish := edgeFinish
    edgeStart₂ := edgeStart₂
    edgeFinish₂ := edgeFinish₂
    mix := mix
    index := index
    nonzeroWitness := nonzeroWitness
    B := B }

def readCertificate : Decoder (Fin 4 → AxisCertificate) := do
  let a ← readAxis
  let b ← readAxis
  let c ← readAxis
  let d ← readAxis
  pure (fun
    | 0 => a
    | 1 => b
    | 2 => c
    | 3 => d)

structure PrecomputedTriangle where
  v : Array Rat

def PrecomputedTriangle.toTriangle (pt : PrecomputedTriangle) :
    AtlasProjectiveView.Triangle Rat :=
  fun i c => pt.v[3 * i.val + c.val]!

def PrecomputedTriangle.ofTriangle (t : AtlasProjectiveView.Triangle Rat) :
    PrecomputedTriangle :=
  let arr : Array Rat := #[
    t 0 0, t 0 1, t 0 2,
    t 1 0, t 1 1, t 1 2,
    t 2 0, t 2 1, t 2 2
  ]
  ⟨arr⟩

def stepTriangle (pt : PrecomputedTriangle) (child : Fin 4) :
    PrecomputedTriangle :=
  let s := split pt.toTriangle child
  let arr : Array Rat := #[
    s 0 0, s 0 1, s 0 2,
    s 1 0, s 1 1, s 1 2,
    s 2 0, s 2 1, s 2 2
  ]
  ⟨arr⟩

def readTrianglePath (length : Nat) (pt : PrecomputedTriangle) :
    Decoder PrecomputedTriangle := fun cursor =>
  Id.run do
    let mut curCursor := cursor
    let mut curPt := pt
    for _ in [0:length] do
      let (child, nextCursor) := curCursor.readNat
      curCursor := nextCursor
      curPt := stepTriangle curPt (fin4 child)
    (curPt, curCursor)

def readTriangle (base : AtlasProjectiveView.Triangle Rat) :
    Decoder (AtlasProjectiveView.Triangle Rat) := do
  let length ← readNat
  let pt ← readTrianglePath length (PrecomputedTriangle.ofTriangle base)
  pure pt.toTriangle

def readRow (base : AtlasProjectiveView.Triangle Rat) : Decoder Row := do
  let tag ← readNat
  let id ← readNat
  let root ← readNat
  let triangle ← readTriangle base
  if tag = 0 then
    let a ← readNat
    let b ← readNat
    let c ← readNat
    let d ← readNat
    pure (.split id ![a, b, c, d] (fin8 root) triangle)
  else if tag = 2 then
    let symmetryIndex ← readNat
    let certificate ← readCertificate
    let c ← readRat
    let δ ← readRat
    let r ← readRat
    let coreAxis ← readAxis
    let d0 ← readRat
    let d1 ← readRat
    let d2 ← readRat
    let defect0 : Fin 3 → ℚ := ![d0, d1, d2]
    let D0 ← readRat
    let r_min ← readRat
    let c_cone ← readRat
    let c_core ← readRat
    let lam ← readRat
    let w0 ← readRat
    let w1 ← readRat
    let w2 ← readRat
    let w : Fin 3 → ℚ := ![w0, w1, w2]
    pure (.decomposed id {
      interval := AtlasPose.rootInterval Rat
      root := fin8 root
      triangle
      chart := 0
      symmetryIndex := fin5 symmetryIndex
      certificate
      c
      δ
      r } coreAxis defect0 D0 r_min c_cone c_core lam w)
  else
    let symmetryIndex ← readNat
    let certificate ← readCertificate
    let c ← readRat
    let δ ← readRat
    let r ← readRat
    pure (.certificate id {
      interval := AtlasPose.rootInterval Rat
      root := fin8 root
      triangle
      chart := 0
      symmetryIndex := fin5 symmetryIndex
      certificate
      c
      δ
      r })

def readRows (base : AtlasProjectiveView.Triangle Rat) (count : Nat) :
    Decoder (Array Row) := fun cursor =>
  Id.run do
    let mut cur := cursor
    let mut rows := Array.mkEmpty count
    for _ in [0:count] do
      let (row, next) := readRow base cur
      cur := next
      rows := rows.push row
    (rows, cur)

def decodeRows (base : AtlasProjectiveView.Triangle Rat)
    (count : Nat) (packed : String) : Array Row :=
  (readRows base count { data := packed.toUTF8 }).1

def decodeTable (initialChild symmetryIndex : Nat) (r : Rat)
    (count : Nat) (packed : String) : Table :=
  let base := split upperWedgeTriangle (fin4 initialChild)
  let rows := decodeRows base count packed
  {
    symmetryIndex := fin5 symmetryIndex
    r
    root := 0
    triangle := base
    get := fun i => rows[i]!
    size := count
  }

structure Decoded where
  symmetryIndex : Nat
  r : Rat
  count : Nat
  rows : Array Row

def readDecoded (base : AtlasProjectiveView.Triangle Rat) :
    Decoder Decoded := do
  let count ← readNat
  let symmetryIndex ← readNat
  let r ← readRat
  let rows ← readRows base count
  pure { symmetryIndex, r, count, rows }

/-- Decode a self-describing packed local-table artifact from binary bytes. -/
def decodePackedByteArray (initialChild : Nat) (data : ByteArray) : Table :=
  let base := split upperWedgeTriangle (fin4 initialChild)
  let decoded := (readDecoded base { data }).1
  {
    symmetryIndex := fin5 decoded.symmetryIndex
    r := decoded.r
    root := 0
    triangle := base
    get := fun i => decoded.rows[i]!
    size := decoded.count
  }

/-- Decode a self-describing packed local-table artifact. The initial projective
root child is supplied by its position in the four-table atlas. -/
def decodePackedTable (initialChild : Nat) (packed : String) : Table :=
  decodePackedByteArray initialChild packed.toUTF8

end Noperthedron.Nopert229.PackedLocalViewTree

end
