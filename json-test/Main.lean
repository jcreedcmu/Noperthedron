import Batteries.Data.Rat
import Lean
open Lean

def loadJsonFile (relPath : System.FilePath) : IO Json := do
  let root ← IO.currentDir
  let path := root / relPath

  let content ← IO.FS.readFile path

  match Json.parse content with
  | Except.ok j     => pure j
  | Except.error err => throw <| IO.userError s!"Failed to parse JSON: {err}"

def toIO {ε α} [ToString ε] (ex : Except ε α) : IO α :=
  match ex with
  | .ok a    => pure a
  | .error e => throw (IO.userError (toString e))

structure Spherical where
  az : Float
  an : Float
deriving FromJson, Repr

structure Cartesian where
  x : Float
  y : Float
  z : Float
deriving FromJson, Repr

structure ViewExample where
  code : String
  mask : String
  ex_spherical : Spherical
  ex_cartesian : Cartesian
deriving FromJson, Repr

abbrev ViewsTestData := Array ViewExample

def main : IO Unit := do
  let jsonTxt ← loadJsonFile "raw_data/views.json"
  let vtd : ViewsTestData ← toIO (FromJson.fromJson? jsonTxt)

  let some fst := vtd[0]? | throw (IO.userError "nope")
  let q : Rat := fst.ex_spherical.an.toRat0
  IO.println s!"Loaded JSON: {repr q}"
