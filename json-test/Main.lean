import Batteries.Data.Rat
import Lean
open Lean

structure RawSpherical where
  az : Float
  an : Float
deriving FromJson, Repr

structure Spherical where
  az : Rat
  an : Rat
deriving Repr

instance : FromJson Spherical where
  fromJson? (json : Json) := do
    let raw : RawSpherical ← FromJson.fromJson? json
    pure { az := raw.az.toRat0, an := raw.an.toRat0 }

structure RawPoint where
  x : Float
  y : Float
deriving FromJson, Repr

structure Point where
  x : Rat
  y : Rat
deriving Repr

instance : FromJson Point where
  fromJson? (json : Json) := do
    let raw : RawPoint ← FromJson.fromJson? json
    pure { x := raw.x.toRat0, y := raw.y.toRat0 }

structure Cartesian where
  x : Float
  y : Float
  z : Float
deriving FromJson, Repr

structure ViewExample where
  -- code : String
  -- mask : String
  ex_spherical : Spherical
  -- ex_cartesian : Cartesian
  ex_hull : Array Point
deriving FromJson, Repr

abbrev ViewsTestData := Array ViewExample

def viewsTestData : Except String ViewExample := do
 let data : String := include_str "../raw_data/views.json"
 let json : Json ← Json.parse data
 let vtd : ViewsTestData ← FromJson.fromJson? json
 let some fst := vtd[0]? | throw "nope"
 pure fst

#eval viewsTestData

def main : IO Unit := do
  IO.println s!"Nop!"
