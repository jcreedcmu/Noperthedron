import Cayley.Checker.KTree

/-!
Untrusted certificate pruning for the original Noperthedron.

Run `lake build nopertPrune`, then:
  .lake/build/bin/nopertPrune INPUT OUTPUT [candidateLimit] [plain|mix]

The output uses the existing certificate format and unchanged Boolean checker.
It is only a proposal until `scripts/cayley/build_certificate.py` completes the kernel proof.
Parsing and serialization follow `cayleyCheck.lean`.
-/

open Cayley
deriving instance Inhabited for K.KTree

/-! ## Parsing -/

/-- Read an integer (optionally negative) starting at byte `i`; returns value and end. -/
def readInt (s : ByteArray) (i : Nat) : Int × Nat := Id.run do
  let mut j := i
  let mut neg := false
  if h : j < s.size then
    if s[j] = 45 then
      neg := true
      j := j + 1
  let mut v : Nat := 0
  for _ in [0:40] do
    if h : j < s.size then
      let c := s[j]
      if 48 ≤ c && c ≤ 57 then
        v := v * 10 + (c.toNat - 48)
        j := j + 1
  return (if neg then -(v : Int) else v, j)

/-- Parse one tree in preorder from position `i` (skipping one separator after each token). -/
def parseTree (s : ByteArray) : Nat → Nat → Option (K.KTree × Nat)
  | 0, _ => none
  | fuel + 1, i =>
    if h : i < s.size then
      let c := s[i]
      if c = 83 then -- 'S'
        let (d, j) := readInt s (i + 1)
        if 0 ≤ d ∧ d < 5 then
          match parseTree s fuel (j + 1) with
          | none => none
          | some (l, k) =>
            match parseTree s fuel k with
            | none => none
            | some (r, m) => some (.split d.toNat l r, m)
        else none
      else if c = 68 then -- 'D'
        let (code, j) := readInt s (i + 1)
        some (.dom code.toNat, j + 1)
      else if c = 71 then -- 'G'
        let (sv, j) := readInt s (i + 1)
        let (w0, k) := readInt s (j + 1)
        let (w1, m) := readInt s (k + 1)
        some (.gap sv.toNat w0 w1, m + 1)
      else none
    else none

/-- Parse the 15 trees. -/
def parseAll (s : ByteArray) : Option (Array K.KTree) := Id.run do
  let mut i := 0
  let mut out : Array K.KTree := #[]
  for _ in [0:15] do
    match parseTree s 200 i with
    | none => return none
    | some (t, j) =>
      out := out.push t
      i := j
  if i < s.size then return none
  return some out

partial def kLeaves : K.KTree → Nat
  | .split _ l r => kLeaves l + kLeaves r
  | _ => 1

partial def kToks (acc : Array String) : K.KTree → Array String
  | .split d l r => kToks (kToks (acc.push s!"S{d}") l) r
  | .dom c => acc.push s!"D{c}"
  | .gap s w0 w1 => acc.push s!"G{s}:{w0}:{w1}"
  | .hole => acc.push "H"

/-- Only an untrusted proposal generator: the exported tree must be rechecked in the kernel. -/
def sameWitness : K.KTree → K.KTree → Bool
  | .dom a, .dom b => a == b
  | .gap s a b, .gap t c d => s == t && a == c && b == d
  | _, _ => false

/-- Share the large intermediate polynomials in native execution. Kernel
reduction already caches many of these expressions; compiled execution does not
share them across calls to the original helper functions. -/
def proposalGap (b : K.KBox) (s : Nat) (w0 w1 : Int) : Bool :=
  if s < 90 then
    let S := K.vS s
    let g := K.pGapData b S w0 w1
    let A := K.gA g
    let err := K.gErr b w0 w1
    let full (tx ty tz : Int) :=
      let F := Int.sub A (Int.mul
        (Int.add (Int.add (Int.mul tx g.a0) (Int.mul ty g.a1)) (Int.mul tz g.a2)) g.kd)
      decide (err ≤ K.pLower F) || K.bernGE F err
    let pair := K.gPair b s
    let pairTest (_ : Unit) :=
      let L := K.gL g
      decide (K.gErrL b w0 w1 ≤ 2 * K.pLower L) ||
        K.bernGE (Int.mul 2 L) (K.gErrL b w0 w1)
    let test (t : Nat) (tx ty tz : Int) :=
      if pair = some t then
        pairTest () || (!decide (b.c.getD 4 0 - b.h.getD 4 0 ≤ 0) && full tx ty tz)
      else full tx ty tz
    let E0 := K.pStats (Int.mul g.a0 g.kd)
    let E1 := K.pStats (Int.mul g.a1 g.kd)
    let E2 := K.pStats (Int.mul g.a2 g.kd)
    let sA := K.pStats A
    let tot : Int := ((E0.c0.natAbs : Int) + E1.c0.natAbs + E2.c0.natAbs) +
      ((E0.abs : Int) + E1.abs + E2.abs)
    let C := K.p2 639 + (sA.c0 - sA.slack - err) - K.p2 170 * tot
    let packOK := decide (0 ≤ C) && decide (C + 2 * K.p2 170 * tot < K.p2 640)
    (w0 != 0 || w1 != 0) && K.nrmOK b w0 w1 &&
      if packOK then
        K.vtxSplit (fun t tx ty tz _ _ _ => test t tx ty tz) 8 0 90
          (Nat.xor K.signT (Nat.land (K.quickV C E0.c0 E1.c0 E2.c0 E0.abs E1.abs E2.abs) K.signT))
      else K.vtxIdx.all fun (t, (tx, ty, tz), _) => test t tx ty tz
  else false

/-- Native proposal acceleration changes evaluation order only. -/
theorem proposalGap_eq (b : K.KBox) (s : Nat) (w0 w1 : Int) :
    proposalGap b s w0 w1 = K.pGapOK b s w0 w1 := by rfl

def proposalOK (b : K.KBox) : K.KTree → Bool
  | .gap s w0 w1 => proposalGap b s w0 w1
  | w => K.kCheck false b w

/-- Cheap proposal filter. It never accepts a replacement on its own: the
unchanged whole-box checker must still accept every proposed merge. -/
def pointOK (b : K.KBox) (x : Fin 5 → Int) : K.KTree → Bool
  | .gap s w0 w1 =>
    let g := K.gapGen Int.add Int.sub Int.mul (fun z => z) x b (K.vS s) w0 w1
    let A := K.gA g
    let err := K.gErr b w0 w1
    let pair := K.gPair b s
    let pairOK := decide (K.gErrL b w0 w1 ≤ 2 * K.gL g)
    K.vtxIdx.all fun (t, (tx, ty, tz), _) =>
      (pair == some t && pairOK) ||
      decide (err ≤ A - (tx*g.a0+ty*g.a1+tz*g.a2)*g.kd)
  | _ => true

def sampleOK (b : K.KBox) (w : K.KTree) : Bool :=
  match w with
  | .gap .. => pointOK b (fun _ => 0) w &&
      (List.range 32).all fun mask =>
        pointOK b (fun i => if mask.testBit i.val then 1 else -1) w
  | _ => true

partial def prune (limit : Nat) (mix : Bool) (b : K.KBox) (t : K.KTree) : K.KTree × Array K.KTree × Nat :=
  match t with
  | .split d l r => Id.run do
    let (l, wl, nl) := prune limit mix (b.split d).1 l
    let (r, wr, nr) := prune limit mix (b.split d).2 r
    let mut ws := wl
    for w in wr do
      if !ws.any (sameWitness w) then ws := ws.push w
    if nl + nr ≤ 256 then
      for w in ws do
        if sampleOK b w && proposalOK b w then return (w, #[w], 1)
      if mix && nl + nr ≤ 64 then
        for i in [:min 4 ws.size] do
          for j in [i+1:min 8 ws.size] do
            match ws[i]!, ws[j]! with
            | .gap s a0 a1, .gap s' b0 b1 =>
              if s == s' then
                for k in [1:4] do
                  let k : Int := k
                  let w := K.KTree.gap s ((k*a0+(4-k)*b0)/4) ((k*a1+(4-k)*b1)/4)
                  if !ws.any (sameWitness w) && sampleOK b w && proposalOK b w then
                    return (w, #[w], 1)
            | _, _ => pure ()
    return (.split d l r, ws.extract 0 (min limit ws.size), nl+nr)
  | _ => (t, #[t], 1)

def main (args : List String) : IO Unit := do
  if args.length < 2 then
    throw (IO.userError "usage: nopertPrune INPUT OUTPUT [candidateLimit] [plain|mix]")
  let input := args[0]!
  let output := args[1]!
  let limit := (args[2]?.getD "8").toNat!
  if limit == 0 then throw (IO.userError "candidateLimit must be positive")
  let mix := args[3]?.getD "plain" == "mix"
  let data ← IO.FS.readFile input
  let some ts := parseAll data.toUTF8 | throw (IO.userError "invalid input tree")
  let mut tasks := #[]
  for r in [0:15] do
    let t := ts[r]!
    tasks := tasks.push (Task.spawn fun _ => prune limit mix (K.rootK r) t)
  let mut out : Array String := #[]
  for r in [0:15] do
    let (t, _, n) := tasks[r]!.get
    let tokens := " ".intercalate (kToks #[] t).toList
    IO.FS.writeFile s!"{output}.root{r}" (tokens ++ "\n")
    out := out.push tokens
    IO.println s!"root {r}: {kLeaves ts[r]!} -> {n} leaves"
    (← IO.getStdout).flush
  IO.FS.writeFile output ("\n".intercalate out.toList ++ "\n")
