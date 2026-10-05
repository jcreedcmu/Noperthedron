module

public import Noperthedron.PentagonalHexecontahedron.DHChecks

@[expose] public section

/-!
# Decoding the deltoidal hexecontahedron's cap and tie certificates (untrusted)

`decodeCert` reads a `capcert --export` file, `decodeTies` the tie data and
`tietube --export_dir` certificates. Nothing here is trusted: the decoded data
is checked natively (`capsCheckPar`, `tiesCheckPar`) before it is used.
-/

namespace Noperthedron.PentagonalHexecontahedron.DHDecode

open Noperthedron.PentagonalHexecontahedron.Cap
open Noperthedron.PentagonalHexecontahedron.Tie
open Noperthedron.PentagonalHexecontahedron.DH

instance : Inhabited IcoQ := ⟨IcoQ.zero⟩
instance : Inhabited Kind := ⟨.fe⟩

/-! ### Untrusted decoding -/

def parseQ (s : String) : ℚ :=
  match s.splitOn "/" with
  | [n] => (n.toInt?.getD 0 : ℚ)
  | [n, d] => (n.toInt?.getD 0 : ℚ) / (d.toNat?.getD 1 : ℚ)
  | _ => 0

def parseK (t : Array String) (i : ℕ) : IcoQ := ⟨parseQ t[i]!, parseQ t[i+1]!, parseQ t[i+2]!, parseQ t[i+3]!⟩
def parseKV (t : Array String) (i : ℕ) : KVec := ![parseK t i, parseK t (i+4), parseK t (i+8)]

def tokens (l : String) : Array String := ((l.splitOn " ").filter (· ≠ "")).toArray

/-- A preorder certificate tree: `S<axis>` split, `L<w>,` witness leaf, `P` prune, `X` cone, `F` fail. -/
partial def parseTree (s : Array Char) (i : ℕ) : CTree × ℕ :=
  match s[i]! with
  | 'S' => let a := s[i+1]!.toNat - '0'.toNat
           let (l, j) := parseTree s (i+2)
           let (r, k) := parseTree s j
           (.split ⟨a % 5, Nat.mod_lt _ (by norm_num)⟩ l r, k)
  | 'L' => Id.run do
           let mut j := i + 1
           let mut n := 0
           while s[j]! != ',' do
             n := n * 10 + (s[j]!.toNat - '0'.toNat)
             j := j + 1
           return (.leaf n, j + 1)
  | 'P' => (.prune, i + 1)
  | 'X' => (.cone, i + 1)
  | _ => (.fail, i + 1)

def kindOf (s : String) : Kind := match s with | "Fe" => .fe | "cone" => .cone | "Mcone" => .mcone | _ => .face

/-- Decodes a `capcert --export` file. -/
def decodeCert (lines : Array String) : CapCert := Id.run do
  let mut V : Array KVec := #[]
  let mut W : Array (ℕ × KVec) := #[]
  let mut x : KVec := fun _ => IcoQ.zero
  let mut e1 := x
  let mut e2 := x
  let mut aniso := false
  let mut halfTurn := false
  let mut tie := false
  let mut mu0 : ℚ := 0
  let mut sscale := 2
  let mut t0 : ℚ := 1/4
  let mut t0m : ℚ := 1/4
  let mut mcm : ℕ := 1
  let mut charts : Array (ChartId × CTree) := #[]
  let mut zl : List ((Kind × ℕ × ℕ × Bool) × ℕ) := []
  let mut tieCharts : List ((Kind × ℕ × ℕ × Bool) × (ℕ × ℕ × ℕ)) := []
  let mut pending : Option ChartId := none
  for l in lines do
    let t := tokens l
    if t.size == 0 then continue
    match t[0]! with
    | "cap" => aniso := t[3]! == "1"; halfTurn := t[5]! == "1"; tie := t[7]! == "1"; mu0 := parseQ t[9]!
               sscale := t[11]!.toNat!; t0 := parseQ t[13]!
               if t.size > 19 then t0m := parseQ t[19]!; mcm := t[21]!.toNat!
    | "frame" => x := parseKV t 1; e1 := parseKV t 13; e2 := parseKV t 25
    | "tie_chart" =>
      tieCharts := tieCharts ++ [((kindOf t[1]!, t[2]!.toNat!, t[3]!.toNat!, t[4]! == "1"),
        (t[5]!.toNat!, t[6]!.toNat!, t[7]!.toNat!))]
    | "vertex" => V := V.push (parseKV t 2)
    | "witness" => W := W.push (t[2]!.toNat!, parseKV t 3)
    | "chart" =>
      let id : ChartId := ⟨kindOf t[1]!, t[2]!.toNat!, t[3]!.toNat!, t[4]! == "1", t[5]!.toNat!, t[6]!.toNat!,
        t[7]! == "1", t[9]!.toNat!⟩
      pending := some id
      let b := (id.kind, id.side, id.axis, id.sign)
      if !(zl.any (fun e => e.1 == b)) then zl := zl ++ [(b, id.z)]
    | "tree" => match pending with
      | some id => charts := charts.push (id, (parseTree t[1]!.toList.toArray 0).1); pending := none
      | none => pure ()
    | _ => pure ()
  -- G = H_x = 2 x xᵀ − I (columns), the half-turn element's matrix (u0).
  let two : IcoQ := IcoQ.ofRat 2
  let G : Fin 3 → KVec := fun j i =>
    IcoQ.sub (IcoQ.mul two (IcoQ.mul (x i) (x j))) (if i = j then IcoQ.one else IcoQ.zero)
  return { st := { aniso, halfTurn, strongScale := sscale, mcm, x, e1, e2, tieCharts },
           pr := ⟨mu0, t0, t0m, tie, true⟩, zList := zl, verts := V, wits := W, usePrune := halfTurn, Gcol := G,
           charts := charts.toList }

/-- Decodes the tie data (`dh_tie_data.txt`), the node index (`nodes.txt`) and the certificates
(`n<n>_t<t>.cert`) into `TieCerts` with leaves in `dhTieNodes` order. -/
def decodeTies (dataLines nodeLines : Array String) (certFiles : Array (ℕ × ℕ × Array String)) : TieCerts :=
  Id.run do
    let mut V : Array KVec := #[]
    let mut X : Array KVec := #[]
    let mut L : Array (Array KVec) := #[]
    let mut Wt : Array (Array (ℕ × KVec)) := #[]
    for l in dataLines do
      let t := tokens l
      if t.size == 0 then continue
      match t[0]! with
      | "V" => V := V.push (parseKV t 2)
      | "X" => X := X.push (parseKV t 2); L := L.push #[]; Wt := Wt.push #[]
      | "L" => let n := t[1]!.toNat!; L := L.set! n (L[n]!.push (parseKV t 3))
      | "W" => let n := t[1]!.toNat!; Wt := Wt.set! n (Wt[n]!.push (t[2]!.toNat!, parseKV t 3))
      | _ => pure ()
    let normals : Array TieNormal := (List.range X.size).toArray.map fun n => ⟨X[n]!, L[n]!, Wt[n]!⟩
    -- Node index: (normal, t, path) ↦ k.
    let mut index : Std.HashMap (ℕ × ℕ × String) ℕ := {}
    let mut count := 0
    for l in nodeLines do
      let t := tokens l
      if t.size < 4 then continue
      let p := if t[2]! == "." then "" else t[2]!
      index := index.insert (t[0]!.toNat!, t[1]!.toNat!, p) t[3]!.toNat!
      count := max count (t[3]!.toNat! + 1)
    let mut leaves : Array (List CTree) := Array.replicate count []
    for (n, tt, lines) in certFiles do
      let mut current : Option ℕ := none
      let mut faces : Array CTree := #[]
      for l in lines do
        let t := tokens l
        if t.size == 0 then continue
        if t[0]! == "node" then
          if let some k := current then leaves := leaves.set! k faces.toList
          faces := #[]
          let p := if t[1]! == "." then "" else t[1]!
          current := if t[2]! == "L" then index.get? (n, tt, p) else none
        else if t[0]! == "face" then
          faces := faces.push (parseTree t[1]!.toList.toArray 0).1
      if let some k := current then leaves := leaves.set! k faces.toList
    return { V, normals, leaves }

def readLines (path : String) : IO (Array String) := IO.FS.lines path

end Noperthedron.PentagonalHexecontahedron.DHDecode
