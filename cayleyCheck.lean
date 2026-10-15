import Cayley.Checker.KTree

/-!
Native driver for the Cayley kernel certificate.

    cayleyCheck kwalk FILE                            -- run `kCheck` natively on the 15 trees
    cayleyCheck kgen FILE OUTDATA OUTLEAN maxLeaves chunksPerModule
                                                      -- write the kernel chunk modules

FILE holds the 15 trees in preorder tokens `S<d>`, `D<code>`, `G<s>:<w0>:<w1>`.
-/

open Cayley

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

/-- Kernel-walk pairs at depth `d` (for parallel native validation). -/
def kFrontier : Nat → K.KBox → K.KTree → List (K.KBox × K.KTree)
  | d + 1, b, .split dim l r => kFrontier d (b.split dim).1 l ++ kFrontier d (b.split dim).2 r
  | _, b, t => [(b, t)]

partial def kLeaves : K.KTree → Nat
  | .split _ l r => kLeaves l + kLeaves r
  | _ => 1

partial def kToks (acc : Array String) : K.KTree → Array String
  | .split d l r => kToks (kToks (acc.push s!"S{d}") l) r
  | .dom c => acc.push s!"D{c}"
  | .gap s w0 w1 => acc.push s!"G{s}:{w0}:{w1}"
  | .hole => acc.push "H"

/-- Cut `t` into maximal subtrees with at most `maxL` leaves; returns the skeleton tokens. -/
partial def kCut (maxL : Nat) (b : K.KBox) (t : K.KTree) (skel : Array String)
    (chunks : Array (K.KBox × K.KTree)) : Array String × Array (K.KBox × K.KTree) :=
  if kLeaves t ≤ maxL then (skel.push "H", chunks.push (b, t))
  else match t with
    | .split d l r =>
      let (s1, c1) := kCut maxL (b.split d).1 l (skel.push s!"S{d}") chunks
      kCut maxL (b.split d).2 r s1 c1
    | _ => (skel.push "H", chunks.push (b, t))

partial def maxK (b : K.KBox) : K.KTree → Nat
  | .split d l r => max (maxK (b.split d).1 l) (maxK (b.split d).2 r)
  | _ => b.K

def main (args : List String) : IO UInt32 := do
  if args[0]! == "kgen" then
    -- kgen DATA OUTDATA OUTLEAN maxLeaves chunksPerModule
    let data ← IO.FS.readFile args[1]!
    let outD := args[2]!
    let outL := args[3]!
    let maxL := args[4]!.toNat!
    let perM := args[5]!.toNat!
    match parseAll data.toUTF8 with
    | none => return 1
    | some ts =>
      IO.FS.createDirAll outD
      IO.FS.createDirAll outL
      let mut all : Array (K.KBox × K.KTree) := #[]
      let mut rootIds : Array (List Nat) := #[]
      for r in [0:15] do
        let (skel, ch) := kCut maxL (K.rootK r) (ts.getD r K.KTree.hole) #[] #[]
        let ids := (List.range ch.size).map (· + all.size)
        IO.FS.writeFile s!"{outD}/skel_{r}.txt"
          (" ".intercalate skel.toList ++ "\n" ++ " ".intercalate (ids.map toString) ++ "\n")
        all := all ++ ch
        rootIds := rootIds.push ids
      let nMod := (all.size + perM - 1) / perM
      for m in [0:nMod] do
        let mut lines : Array String := #[]
        for i in [m * perM : min ((m + 1) * perM) all.size] do
          let (b, t) := all.getD i (K.rootK 0, K.KTree.hole)
          let hdr := [toString i, toString b.chart, toString b.face, toString b.K] ++
            b.c.map toString ++ b.h.map toString
          lines := lines.push (" ".intercalate (hdr ++ (kToks #[] t).toList))
        IO.FS.writeFile s!"{outD}/c_{m}.txt" ("\n".intercalate lines.toList ++ "\n")
        IO.FS.writeFile s!"{outL}/C{m}.lean" s!"module

public import CayleyKernel.Load
public meta import CayleyKernel.Load

@[expose] public section

/-! GENERATED (`cayleyCheck kgen`): kernel-checked chunks {m * perM}–{min ((m + 1) * perM) all.size - 1}. -/

set_option Elab.async false

namespace Cayley.KProof

cayley_chunks \"{outD}/c_{m}.txt\"

end Cayley.KProof

end
"
      let modName (outL : String) : String := (outL.replace "/" ".")
      for r in [0:15] do
        let ids := rootIds[r]!
        let mods := (ids.map (· / perM)).eraseDups
        let imps := "\n".intercalate (mods.map fun m => s!"public import {modName outL}.C{m}")
        IO.FS.writeFile s!"{outL}/R{r}.lean" s!"module

public import CayleyKernel.Load
public meta import CayleyKernel.Load
{imps}

@[expose] public section

/-! GENERATED (`cayleyCheck kgen`): root box {r}. -/

set_option Elab.async false

namespace Cayley.KProof

cayley_root {r} \"{outD}/skel_{r}.txt\"

end Cayley.KProof

end
"
      IO.FS.writeFile s!"{outL}/All.lean" ("module\n\n" ++ "\n".intercalate
        ((List.range 15).map fun r => s!"public import {modName outL}.R{r}") ++ "\n")
      IO.println s!"kgen: {all.size} chunks in {nMod} modules"
      return 0
  if args[0]! == "kwalk" then
    let data ← IO.FS.readFile args[1]!
    match parseAll data.toUTF8 with
    | none => return 1
    | some ts =>
      let t0 ← IO.monoMsNow
      let mut tasks := #[]
      let mut mk := 0
      for r in [0:15] do
        let kt := (ts.getD r K.KTree.hole)
        mk := max mk (maxK (K.rootK r) kt)
        for (b, t) in kFrontier 10 (K.rootK r) kt do
          tasks := tasks.push (r, Task.spawn fun _ => K.kCheck false b t)
      let mut bad := 0
      for (r, t) in tasks do
        if !t.get then
          bad := bad + 1
          if bad ≤ 5 then IO.println s!"kwalk reject in root {r}"
      let t1 ← IO.monoMsNow
      IO.println s!"kwalk: {tasks.size} tasks, {bad} rejected, max K {mk}, {t1 - t0} ms"
      return 0
  IO.println "usage: cayleyCheck (kwalk FILE | kgen FILE OUTDATA OUTLEAN maxLeaves chunksPerModule)"
  return 1
