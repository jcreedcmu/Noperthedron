import Noperthedron.Nopert231.AtlasProjectiveGlobalCertificate
import Noperthedron.Nopert231.AtlasProjectiveMixedGlobalCertificate
import Noperthedron.Nopert231.PackedSolutionTree

/-!
Golden values for the C++ port `nopert229/exact5d.{h,cc}`: reads boxes, one
per line, and prints Lean's values of the checker quantities so that
`exact5d_test` can compare them exactly.

Input lines (whitespace separated; rationals as `n` or `n/d`):

  G chart t00 t01 t02 t10 t11 t12 t20 t21 t22 cx cy cz rx ry rz CERT i0 i1 i2 lambda
  M chart t00 .. t22 cx cy cz rx ry rz (CERT i0 i1 i2 lambda)x4 w0 w1 w2 w3

where the Cayley box is center ± |radius| and
CERT = es0 es1 es2 ef0 ef1 ef2 es20 es21 es22 ef20 ef21 ef22 m0 m1 m2 x0 x1 x2 nz0 nz1 nz2 B.

Output for G: `supportUpper` for i in 0..2, k in 0..19 (60 values), then
weightLower x3, weightUpper x3, weightedDefectUpper, bernsteinDisplacementLower,
adjustedDisplacementBall center, radius, certifiedDisplacementLower, dBound,
displacementError, admissible (0/1), valid (0/1).
Output for M: bernsteinDisplacementLower, weightedDefectUpper, valid (0/1).

  P chart cx cy cz rx ry rz r

Output for P: outsideCayleyBall (0/1), fundamental-prune lower bound for
direction positive and negative, their validity (0/1 each), the chart-0
identity tube's mismatchRadius, and Tube.Valid for radius r (0/1).
-/

open Noperthedron.Nopert231
open Noperthedron.Nopert231.AtlasProjectiveLocalCertificate

deriving instance Inhabited for AxisCertificate
deriving instance Inhabited for AtlasProjectiveMixedGlobalCertificate.Component

def parseRat (s : String) : ℚ :=
  match s.splitOn "/" with
  | [n] => (n.toInt! : ℚ)
  | [n, d] => (n.toInt! : ℚ) / (d.toNat! : ℚ)
  | _ => 0

def fin3 (n : Nat) : Fin 3 := ⟨n % 3, by omega⟩
def fin4 (n : Nat) : Fin 4 := ⟨n % 4, by omega⟩
def fin20 (n : Nat) : Fin 20 := ⟨n % 20, by omega⟩
def fin1001 (n : Nat) : Fin 1001 := ⟨n % 1001, by omega⟩

structure Toks where
  toks : Array String
  pos : Nat := 0

def Toks.next (t : Toks) : String × Toks := (t.toks[t.pos]!, { t with pos := t.pos + 1 })
def Toks.rat (t : Toks) : ℚ × Toks := let (s, t) := t.next; (parseRat s, t)
def Toks.nat (t : Toks) : Nat × Toks := let (s, t) := t.next; (s.toNat!, t)

def Toks.vertices (t : Toks) : (Fin 3 → VertexIndex) × Toks :=
  let (a, t) := t.nat
  let (b, t) := t.nat
  let (c, t) := t.nat
  (![fin20 a, fin20 b, fin20 c], t)

def Toks.axis (t : Toks) : AxisCertificate × Toks :=
  let (es, t) := t.vertices
  let (ef, t) := t.vertices
  let (es2, t) := t.vertices
  let (ef2, t) := t.vertices
  let (m0, t) := t.nat
  let (m1, t) := t.nat
  let (m2, t) := t.nat
  let (ix, t) := t.vertices
  let (nz, t) := t.vertices
  let (b, t) := t.rat
  ({ edgeStart := es, edgeFinish := ef, edgeStart₂ := es2, edgeFinish₂ := ef2,
     mix := ![fin1001 m0, fin1001 m1, fin1001 m2], index := ix,
     nonzeroWitness := nz, B := b }, t)

def Toks.triangle (t : Toks) : AtlasProjectiveView.Triangle ℚ × Toks := Id.run do
  let mut t := t
  let mut v : Array ℚ := #[]
  for _ in [0:9] do
    let (q, t') := t.rat
    v := v.push q
    t := t'
  (![![v[0]!, v[1]!, v[2]!], ![v[3]!, v[4]!, v[5]!], ![v[6]!, v[7]!, v[8]!]], t)

def Toks.interval (t : Toks) : AtlasProjectiveSolutionTree.Interval × Toks :=
  let (cx, t) := t.rat
  let (cy, t) := t.rat
  let (cz, t) := t.rat
  let (rx, t) := t.rat
  let (ry, t) := t.rat
  let (rz, t) := t.rat
  (PackedSolutionTree.relativeInterval ![cx, cy, cz] ![rx, ry, rz], t)

def b2n (b : Bool) : String := if b then "1" else "0"

def globalLine (t : Toks) : String := Id.run do
  let (chart, t) := t.nat
  let (tri, t) := t.triangle
  let (iv, t) := t.interval
  let (cert, t) := t.axis
  let (i0, t) := t.nat
  let (i1, t) := t.nat
  let (i2, t) := t.nat
  let (lam, _) := t.rat
  let box : AtlasProjectiveGlobalCertificate.Box := {
    interval := iv, root := 0, triangle := tri, chart := fin4 chart,
    certificate := cert, innerIndex := ![fin20 i0, fin20 i1, fin20 i2],
    ballMultiplier := lam }
  let mut out : Array String := #[]
  for i in [0:3] do
    for k in [0:20] do
      out := out.push (toString (box.supportUpper (fin3 i) (fin20 k)))
  for i in [0:3] do out := out.push (toString (box.weightLower (fin3 i)))
  for i in [0:3] do out := out.push (toString (box.weightUpper (fin3 i)))
  out := out.push (toString box.weightedDefectUpper)
  out := out.push (toString box.bernsteinDisplacementLower)
  out := out.push (toString box.adjustedDisplacementBall.center)
  out := out.push (toString box.adjustedDisplacementBall.radius)
  out := out.push (toString box.certifiedDisplacementLower)
  out := out.push (toString box.dBound)
  out := out.push (toString box.displacementError)
  out := out.push (b2n (decide box.Admissible))
  out := out.push (b2n (decide box.Valid))
  " ".intercalate out.toList

def mixedLine (t : Toks) : String := Id.run do
  let (chart, t) := t.nat
  let (tri, t) := t.triangle
  let (iv, t) := t.interval
  let mut t := t
  let mut comps : Array AtlasProjectiveMixedGlobalCertificate.Component := #[]
  for _ in [0:4] do
    let (cert, t1) := t.axis
    let (i0, t1) := t1.nat
    let (i1, t1) := t1.nat
    let (i2, t1) := t1.nat
    let (lam, t1) := t1.rat
    comps := comps.push { certificate := cert, innerIndex := ![fin20 i0, fin20 i1, fin20 i2],
                          ballMultiplier := lam }
    t := t1
  let mut w : Array ℚ := #[]
  for _ in [0:4] do
    let (q, t1) := t.rat
    w := w.push q
    t := t1
  let box : AtlasProjectiveMixedGlobalCertificate.Box := {
    interval := iv, root := 0, triangle := tri, chart := fin4 chart,
    component := ![comps[0]!, comps[1]!, comps[2]!, comps[3]!],
    weight := ![w[0]!, w[1]!, w[2]!, w[3]!] }
  s!"{box.bernsteinDisplacementLower} {box.weightedDefectUpper} {b2n (decide box.Valid)}"

def pruneLine (t : Toks) : String :=
  let (chart, t) := t.nat
  let (iv, t) := t.interval
  let (r, _) := t.rat
  let pos : AtlasFundamentalPrune.Box := { interval := iv, chart := fin4 chart, direction := .positive }
  let neg : AtlasFundamentalPrune.Box := { interval := iv, chart := fin4 chart, direction := .negative }
  let tube : AtlasProjectiveLocalViewTree.Tube := { interval := iv, chart := 0, symmetryIndex := 0, r }
  s!"{b2n (decide (AtlasProjectiveSolutionTree.Interval.outsideCayleyBall iv))} " ++
    s!"{pos.lower} {neg.lower} {b2n (decide pos.Valid)} {b2n (decide neg.Valid)} " ++
    s!"{tube.mismatchRadius} {b2n (decide tube.Valid)}"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let toks := (line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.toArray
  if toks.size > 0 then
    let t : Toks := { toks, pos := 1 }
    let out :=
      if toks[0]! == "G" then globalLine t
      else if toks[0]! == "P" then pruneLine t
      else mixedLine t
    stdout.putStrLn out
    stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
