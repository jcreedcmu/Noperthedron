import Lean.Data.Json.Parser
import Mathlib.Data.String.Defs
import Noperthedron.SolutionTable.Defs

namespace Noperthedron.Solution

def parseNat (name : String) : String → Except String Nat
| "" => Except.ok 0
| s => do
  let .ok v := Lean.Json.Parser.num.run s | throw s!"failed to parse {name} from `{s}`"
  pure (v.mantissa.toNat / 10 ^ v.exponent)

/-- info: Except.ok 0 -/
#guard_msgs in
#eval parseNat "x" "0"

/-- info: Except.ok 1 -/
#guard_msgs in
#eval parseNat "x" "1"

/-- info: Except.ok 100000 -/
#guard_msgs in
#eval parseNat "x" "1e+5"

/-- info: Except.ok 1200000 -/
#guard_msgs in
#eval parseNat "x" "1.2e+6"

def parseInt (name : String) : String → Except String Int
| "" => Except.ok 0
| s => do
  let .some v := s.toInt? | throw s!"failed to parse {name} from '{s}'"
  pure v

/-- Parse a vertex-index column: a natural number `< 90`, decoded via `VertexIndex.ofFin90`. -/
def parseVertexIndex (name s : String) : Except String VertexIndex := do
  let n ← parseNat name s
  if h : n < 90 then pure (VertexIndex.ofFin90 ⟨n, h⟩)
  else throw s!"invalid index for {name}: {n}"

/-
27 columns:
ID,nodeType,nrChildren,IDfirstChild,split,
T1_min,T1_max,V1_min,V1_max,T2_min,T2_max,V2_min,V2_max,
A_min,A_max,
P1_index,P2_index,P3_index,
Q1_index,Q2_index,Q3_index,
r,sigma_Q,
wx_nominator,wy_nominator,w_denominator,
S_index
-/

def parseRowCsv (s : String) : Except String Row := do
  let cols := s.splitOn ","
  let id_str::type_str::nr_children_str::rest := cols | throw "not enough columns"

  let node_id ← parseNat "node_id" id_str
  let .some node_type := type_str.toNat? | throw "failed to parse node_type"
  let nr_children ← parseNat "nr_children" nr_children_str
  let id_fst_child_str::split_str::rest := rest | throw "not enough columns"
  let id_fst_child ← parseNat "id_fst_child" id_fst_child_str
  let split ← parseNat "split" split_str

  let t1min_str::t1max_str::v1min_str::v1max_str::rest := rest | throw "not enough columns"
  let .some t1min := t1min_str.toInt? | throw "failed to parse t1min"
  let .some t1max := t1max_str.toInt? | throw "failed to parse t1max"
  let .some v1min := v1min_str.toInt? | throw "failed to parse v1min"
  let .some v1max := v1max_str.toInt? | throw "failed to parse v1max"

  let t2min_str::t2max_str::v2min_str::v2max_str::rest := rest | throw "not enough columns"
  let .some t2min := t2min_str.toInt? | throw "failed to parse t2min"
  let .some t2max := t2max_str.toInt? | throw "failed to parse t2max"
  let .some v2min := v2min_str.toInt? | throw "failed to parse v2min"
  let .some v2max := v2max_str.toInt? | throw "failed to parse v2max"

  let amin_str::amax_str::rest := rest | throw "not enough columns"
  let .some amin := amin_str.toInt? | throw "failed to parse amin"
  let .some amax := amax_str.toInt? | throw "failed to parse amax"

  let pmin : Pose ℤ := { θ₁ := t1min, θ₂ := t2min, φ₁ := v1min, φ₂ := v2min, α := amin }
  let pmax : Pose ℤ := { θ₁ := t1max, θ₂ := t2max, φ₁ := v1max, φ₂ := v2max, α := amax }
  let interval ← if h : t1min ≤ t1max ∧ t2min ≤ t2max ∧ v1min ≤ v1max ∧ v2min ≤ v2max ∧
                        amin ≤ amax
                 then pure (Interval.ofIntPose pmin pmax ((Pose.le_iff _ _).mpr h))
                 else throw "invalid interval"

  let p1i_str::p2i_str::p3i_str::rest := rest | throw "not enough columns"
  let p1i ← parseVertexIndex "p1i" p1i_str
  let p2i ← parseVertexIndex "p2i" p2i_str
  let p3i ← parseVertexIndex "p3i" p3i_str

  let q1i_str::q2i_str::q3i_str::rest := rest | throw "not enough columns"
  let q1i ← parseVertexIndex "q1i" q1i_str
  let q2i ← parseVertexIndex "q2i" q2i_str
  let q3i ← parseVertexIndex "q3i" q3i_str

  let r_str :: sigmaq_str :: rest := rest | throw "not enough columns"
  let r' ← parseInt "r_str" r_str
  let sigmaqN ← parseNat "sigmaq" sigmaq_str
  let sigmaq : Finset.Icc 0 1 ←
    match sigmaqN with
    | 0 => pure (⟨0, by grind⟩ : Finset.Icc 0 1)
    | 1 => pure (⟨1, by grind⟩ : Finset.Icc 0 1)
    | _ => throw s!"bad sigmaq: {sigmaqN}"

  let wxnum_str::wynum_str::wden_str::rest := rest | throw "not enough columns"
  let wxnum ← parseInt "wxnum" wxnum_str
  let wynum ← parseInt "wynum" wynum_str
  let wden ← parseNat "wden" wden_str

  let sindex_str :: rest := rest | throw "not enough columns"
  let sindex ← parseVertexIndex "sindex" sindex_str

  let [] := rest | throw "too many columns"

  return {
    ID := node_id
    nodeType := node_type
    nrChildren := nr_children
    IDfirstChild := id_fst_child
    split := split
    interval := interval
    S_index := sindex
    wx_numerator := wxnum
    wy_numerator := wynum
    w_denominator := wden
    P1_index := p1i
    P2_index := p2i
    P3_index := p3i
    Q1_index := q1i
    Q2_index := q2i
    Q3_index := q3i
    r' := r'
    sigma_Q := sigmaq
  }

--#eval parseRowCsv "1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,1,24,25,26,27"

def parseSolutionTable (s : String) : Except String Table := do
  let mut result : Array Row := #[]
  for line in s.lines.drop 1 do
    let row ← parseRowCsv line.toString
    result := result.push row
  return result

/-- Parse a contiguous range of lines into rows. -/
private def parseChunk (lns : Array String.Slice) (start stop : ℕ) :
    Except String (Array Row) := Id.run do
  let mut out : Array Row := Array.mkEmpty (stop - start)
  for ln in lns.extract start stop do
    match parseRowCsv ln.toString with
    | .ok row => out := out.push row
    | .error e => return .error e
  return .ok out

/-- Parallel version of `parseSolutionTable`: split the lines after the header
into `nTasks` contiguous chunks, parse each chunk in its own `Task`, and
concatenate the results in order. No correctness lemmas are needed: every
property of the resulting table that the proofs rely on is checked downstream
(by `Table.rowsValidParB` etc.), so the parser need not be trusted. -/
def parseSolutionTablePar (s : String) (nTasks : ℕ) : Except String Table := Id.run do
  let mut lns : Array String.Slice := #[]
  for ln in s.lines do
    lns := lns.push ln
  let n := lns.size
  let chunkSize := (n - 1) / nTasks + 1
  -- index 0 is the header line, so chunk `t` covers lines [1 + t * chunkSize, 1 + (t+1) * chunkSize)
  let tasks := (List.range nTasks).map fun t =>
    Task.spawn fun _ => parseChunk lns (1 + t * chunkSize) (min n (1 + (t + 1) * chunkSize))
  let mut result : Array Row := Array.mkEmpty (n - 1)
  for tsk in tasks do
    match tsk.get with
    | .ok rows => result := result ++ rows
    | .error e => return .error e
  return .ok result
