import Cayley.Checker.Check
import Cayley.Checker.KTree

/-!
Native driver for the Cayley checker (benchmarking and validation).

    cayleyCheck FILE ROOT   -- FILE holds one tree, checked against root box ROOT (0..14)
    cayleyCheck FILE        -- FILE holds all 15 trees
-/

open Cayley

def countLeaves : Tree → Nat
  | .split _ l r => countLeaves l + countLeaves r
  | _ => 1

/-- Collect failing leaves (sequentially) for diagnostics. -/
partial def failures (b : Box) : Tree → Array (Box × Tree)
  | .split d l r => let (bl, br) := b.split d; failures bl l ++ failures br r
  | t => if leafOK b t then #[] else #[(b, t)]

def showTree : Tree → String
  | .dom c => s!"D{c}"
  | .gap s a b => s!"G{s}:{a}:{b}"
  | .fail => "F"
  | .split d _ _ => s!"S{d}"

def microProfile (b : Box) (s : Nat) (w0 w1 : Int) : IO Unit := do
  let reps := 200
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for i in [0:reps] do
    let bp := ({ b with face := b.face + 0 * i } : Box).polys
    acc := acc + (P.lower bp.dr).m.natAbs % 2
  let t1 ← IO.monoNanosNow
  let bp := b.polys
  for i in [0:reps] do
    let wd0 : QI := ((w0 + 0 * i : Int) : QI)
    let wd1 : QI := (w1 : QI)
    let α : V3 P := ⟨P.add (P.sm wd0 bp.no.a00) (P.sm wd1 bp.no.a10),
      P.add (P.sm wd0 bp.no.a01) (P.sm wd1 bp.no.a11), P.add (P.sm wd0 bp.no.a02) (P.sm wd1 bp.no.a12)⟩
    let A := α.dot (bp.mnr.mulVecC vertexTab[s]!)
    acc := acc + (Poly.constCoeff 5 A).m.natAbs % 2
  let t2 ← IO.monoNanosNow
  for i in [0:reps] do
    let ok := gapOK b bp s (w0 + 0 * i) w1
    acc := acc + (if ok then 1 else 0)
  let t3 ← IO.monoNanosNow
  -- how many outer vertices pass the quick test
  let wd0 : QI := (w0 : QI)
  let wd1 : QI := (w1 : QI)
  let α : V3 P := ⟨P.add (P.sm wd0 bp.no.a00) (P.sm wd1 bp.no.a10),
    P.add (P.sm wd0 bp.no.a01) (P.sm wd1 bp.no.a11), P.add (P.sm wd0 bp.no.a02) (P.sm wd1 bp.no.a12)⟩
  let A := α.dot (bp.mnr.mulVecC vertexTab[s]!)
  let kdr := P.sm (chartK b.chart) bp.dr
  let E : V3 P := ⟨P.mul α.x kdr, P.mul α.y kdr, P.mul α.z kdr⟩
  let c0 (q : P) : QI := Poly.constCoeff 5 q
  let sl (q : P) : QI := Poly.absSum 5 q - Poly.dabs (c0 q)
  let mut nq := 0
  for t in [0:90] do
    let T := vertexTab[t]!
    let quick := c0 A - (T.x * c0 E.x + T.y * c0 E.y + T.z * c0 E.z) -
          (sl A + Poly.dabs T.x * sl E.x + Poly.dabs T.y * sl E.y + Poly.dabs T.z * sl E.z)
    if 0 ≤ quick then nq := nq + 1
  IO.println s!"quick passes {nq}/90; slack A {(sl A).m} const A {(c0 A).m}"
  IO.println s!"polys {(t1-t0)/reps/1000} us, A {(t2-t1)/reps/1000} us, gapOK {(t3-t2)/reps/1000} us ({acc})"

def toKT : Tree → K.KTree
  | .split d l r => .split d.val (toKT l) (toKT r)
  | .dom c => .dom c
  | .gap s w0 w1 => .gap s w0 w1
  | .fail => .hole

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

partial def leaves (b : Box) : Tree → Array (Box × Tree)
  | .split d l r => let (bl, br) := b.split d; leaves bl l ++ leaves br r
  | t => #[(b, t)]

def profile (root : Nat) (t : Tree) : IO Unit := do
  let ls := leaves (rootBox root) t
  let mut tg := 0
  let mut ng := 0
  let mut td : Array Nat := Array.replicate 70 0
  let mut nd : Array Nat := Array.replicate 70 0
  for (b, l) in ls.toList.take 400 do
    let t0 ← IO.monoNanosNow
    let ok := leafOK b l
    let t1 ← IO.monoNanosNow
    if !ok then IO.println "fail"
    match l with
    | .gap .. => tg := tg + (t1 - t0); ng := ng + 1
    | .dom c => td := td.modify c (· + (t1 - t0)); nd := nd.modify c (· + 1)
    | _ => pure ()
  IO.println s!"gap leaves {ng}: avg {tg / max ng 1 / 1000} us"
  match ls.toList.find? (fun x => match x.2 with | .gap .. => true | _ => false) with
  | some (b, .gap s w0 w1) => microProfile b s w0 w1
  | _ => pure ()
  for c in [0:70] do
    if nd[c]! > 0 then IO.println s!"dom {c} n {nd[c]!}: avg {td[c]! / nd[c]! / 1000} us"

def dyLit (d : QI) : String := s!"(QI.mk ({d.m}) {d.e})"

def boxLit (b : Box) : String :=
  let v (a : Vector QI 5) := ", ".intercalate (a.toList.map dyLit)
  s!"\{ chart := {b.chart}, face := {b.face}, c := ⟨#[{v b.c}], rfl⟩, h := ⟨#[{v b.h}], rfl⟩ }"

def treeLit : Tree → String
  | .dom c => s!"(.dom {c})"
  | .gap s a b => s!"(.gap {s} ({a}) ({b}))"
  | .fail => ".fail"
  | .split d l r => s!"(.split {d} {treeLit l} {treeLit r})"

def main (args : List String) : IO UInt32 := do
  if args[0]! == "kemit" then
    let data ← IO.FS.readFile args[1]!
    let root := args[2]!.toNat!
    let stride := args[3]!.toNat!
    let n := args[4]!.toNat!
    match parseAll data.toUTF8 with
    | none => return 1
    | some ts =>
      let want := if args.length > 5 then args[5]! else "gap"
      let ls := (leaves (rootBox root) ts[root]!).filter (fun x => match x.2 with
        | .gap .. => want == "gap" | .dom _ => want == "dom" | _ => false)
      for k in [0:n] do
        match ls.getD ((k * stride) % ls.size) (rootBox 0, .fail) with
        | (b, .gap s w0 w1) =>
          let kb := K.ofBox b
          let fn := if args.length > 6 then args[6]! else "kGapOK"
          IO.println s!"example : K.{fn} ⟨{kb.chart}, {kb.face}, {kb.K}, {kb.c}, {kb.h}⟩ {s} ({w0}) ({w1}) = true := by decide +kernel"
        | (b, .dom c) =>
          let kb := K.ofBox b
          let fn := if args.length > 6 then args[6]! else "kDomOK"
          IO.println s!"example : K.{fn} ⟨{kb.chart}, {kb.face}, {kb.K}, {kb.c}, {kb.h}⟩ {c} = true := by decide +kernel"
        | _ => pure ()
      return 0
  if args[0]! == "kfull" then
    let data ← IO.FS.readFile args[1]!
    let stride := args[2]!.toNat!
    let single := if args.length > 3 then some args[3]!.toNat! else none
    let parsed : Option (Array Tree) := match single with
      | none => parseAll data.toUTF8
      | some r => (parseTree data.toUTF8 200 0).map fun (t, _) => (Array.replicate 15 Tree.fail).set! r t
    match parsed with
    | none => return 1
    | some ts =>
      let mut n := 0
      let mut nq := 0
      let mut nl := 0
      let mut nf := 0
      let mut nF1 := 0
      let mut nF2 := 0
      let mut nT := 0
      let mut nTL := 0
      let mut nZero := 0
      let mut nQ := 0
      for r in [0:15] do
        let ls := leaves (rootBox r) ts[r]!
        for k' in [0:ls.size / stride] do
          match ls.getD (k' * stride) (rootBox 0, Tree.fail) with
          | (b, Tree.gap s w0 w1) =>
            n := n + 1
            let kb := K.ofBox b
            let g := K.gapData kb (K.vtxI.getD s (0,0,0)) w0 w1
            let κ := K.chartKI kb.chart
            let W : Int := w0.natAbs + w1.natAbs
            let err : Int := 128 * κ * W * K.p2 (g.sc + 100)
            let A := K.stats3 g.a0 g.a1 g.a2 g.b0 g.b1 g.b2
            let aS : Int := A.l0.natAbs + A.l1.natAbs + A.l2.natAbs + A.l3.natAbs + A.l4.natAbs + A.nl
            let kdS := K.Y27.absSum g.kd
            let e0 (a : K.X6) : Int := a.f0 * g.kd.f0
            let eS (a : K.X6) : Int := K.X6.absSum a * kdS - (e0 a).natAbs
            -- triangle bound on A's slack, no table
            let triS : Int := K.X6.absSum g.a0 * K.Y27.absSum g.b0 - (g.a0.f0 * g.b0.f0).natAbs +
              K.X6.absSum g.a1 * K.Y27.absSum g.b1 - (g.a1.f0 * g.b1.f0).natAbs +
              K.X6.absSum g.a2 * K.Y27.absSum g.b2 - (g.a2.f0 * g.b2.f0).natAbs
            -- triangle bound on A's nonlinear part
            let xlin (a : K.X6) : Int := (a.f1).natAbs + (a.f2).natAbs
            let ylin (b : K.Y27) : Int := (b.f1).natAbs + (b.f3).natAbs + (b.f9).natAbs
            let triN1 (a : K.X6) (b : K.Y27) : Int :=
              K.X6.absSum a * K.Y27.absSum b - (a.f0 * b.f0).natAbs - (a.f0).natAbs * ylin b - (b.f0).natAbs * xlin a
            let triN := triN1 g.a0 g.b0 + triN1 g.a1 g.b1 + triN1 g.a2 g.b2
            let mut leafFull := 0
            for (tx, ty, tz) in K.vtxI do
              let c0 := A.c0 - (tx * e0 g.a0 + ty * e0 g.a1 + tz * e0 g.a2)
              let quickT := c0 - (triS + tx.natAbs * eS g.a0 + ty.natAbs * eS g.a1 + tz.natAbs * eS g.a2)
              if decide (err ≤ quickT) then nT := nT + 1 else
                let x := ((g.a0.smul tx).add (g.a1.smul ty)).add (g.a2.smul tz)
                let k := g.kd
                let el0 := x.f1 * k.f0
                let el1 := x.f2 * k.f0
                let el2 := x.f0 * k.f1
                let el3 := x.f0 * k.f3
                let el4 := x.f0 * k.f9
                let ec := x.f0 * k.f0
                let enl := K.X6.absSum x * kdS - ec.natAbs - el0.natAbs - el1.natAbs - el2.natAbs - el3.natAbs - el4.natAbs
                let lin : Int := (A.l0 - el0).natAbs + (A.l1 - el1).natAbs + (A.l2 - el2).natAbs + (A.l3 - el3).natAbs + (A.l4 - el4).natAbs
                if decide (err ≤ c0 - lin - (triN + enl)) then nTL := nTL + 1 else leafFull := leafFull + 1
            if leafFull == 0 then nZero := nZero + 1
            for (tx, ty, tz) in K.vtxI do
              let c0 := A.c0 - (tx * e0 g.a0 + ty * e0 g.a1 + tz * e0 g.a2)
              let quick := c0 - (aS + tx.natAbs * eS g.a0 + ty.natAbs * eS g.a1 + tz.natAbs * eS g.a2)
              if decide (err ≤ quick) then nq := nq + 1 else
                let x := ((g.a0.smul tx).add (g.a1.smul ty)).add (g.a2.smul tz)
                let k := g.kd
                let el0 := x.f1 * k.f0
                let el1 := x.f2 * k.f0
                let el2 := x.f0 * k.f1
                let el3 := x.f0 * k.f3
                let el4 := x.f0 * k.f9
                let ec := x.f0 * k.f0
                let enl := K.X6.absSum x * kdS - ec.natAbs - el0.natAbs - el1.natAbs - el2.natAbs - el3.natAbs - el4.natAbs
                let lin : Int := (A.l0 - el0).natAbs + (A.l1 - el1).natAbs + (A.l2 - el2).natAbs + (A.l3 - el3).natAbs + (A.l4 - el4).natAbs
                if decide (err ≤ c0 - lin - (A.nl + enl)) then nl := nl + 1 else
                  nf := nf + 1
                  -- candidate middle tiers
                  let kd := g.kd
                  let γ0 := g.b0.sub (kd.smul tx)
                  let γ1 := g.b1.sub (kd.smul ty)
                  let γ2 := g.b2.sub (kd.smul tz)
                  let yc := ((γ0.smul g.a0.f0).add (γ1.smul g.a1.f0)).add (γ2.smul g.a2.f0)
                  let f1 := yc.lower - (g.a0.slack * γ0.absSum + g.a1.slack * γ1.absSum + g.a2.slack * γ2.absSum)
                  if decide (err ≤ f1) then nF1 := nF1 + 1
                  let xc := ((g.a0.smul γ0.f0).add (g.a1.smul γ1.f0)).add (g.a2.smul γ2.f0)
                  let xlow := xc.f0 - xc.slack
                  let f2 := xlow - (γ0.slack * g.a0.absSum + γ1.slack * g.a1.absSum + γ2.slack * g.a2.absSum)
                  if decide (err ≤ f2) then nF2 := nF2 + 1
                  -- quadratic-exact tier
                  let qb := K.quadBound g tx ty tz
                  if decide (err ≤ qb) then nQ := nQ + 1
          | _ => pure ()
      IO.println s!"{n} gap leaves: per leaf quick {nq.toFloat / n.toFloat} lin {nl.toFloat / n.toFloat} full {nf.toFloat / n.toFloat}; of fulls, F1 passes {nF1} F2 passes {nF2} of {nf}; triangle-quick {nT.toFloat / n.toFloat} triangle-lin {nTL.toFloat / n.toFloat} leaves needing no table {nZero}; quad tier passes {nQ} of fulls"
      return 0
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
        let (skel, ch) := kCut maxL (K.rootK r) (toKT ts[r]!) #[] #[]
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
        let kt := toKT ts[r]!
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
  if args[0]! == "kbits" then
    let data ← IO.FS.readFile args[1]!
    let stride := args[2]!.toNat!
    match parseAll data.toUTF8 with
    | none => return 1
    | some ts =>
      let bits (l : List Int) : Nat := l.foldl (fun m x => max m (Nat.log2 x.natAbs + 1)) 0
      let mut mK := 0
      let mut ma := 0
      let mut mb := 0
      let mut mk := 0
      let mut ml := 0
      let mut mw := 0
      for r in [0:15] do
        let ls := leaves (rootBox r) ts[r]!
        for k' in [0:ls.size / stride] do
          match ls.getD (k' * stride) (rootBox 0, Tree.fail) with
          | (b, Tree.gap s w0 w1) =>
            let kb := K.ofBox b
            let g := K.gapData kb (K.vtxI.getD s (0,0,0)) w0 w1
            mK := max mK kb.K
            mw := max mw (bits [w0, w1])
            ma := max ma (bits (g.a0.toList ++ g.a1.toList ++ g.a2.toList))
            mb := max mb (bits (g.b0.toList ++ g.b1.toList ++ g.b2.toList))
            mk := max mk (bits g.kd.toList)
            ml := max ml (bits (g.l0.toList ++ g.l1.toList ++ g.l2.toList))
          | _ => pure ()
      IO.println s!"maxK {mK} w {mw} a {ma} b {mb} kd {mk} l {ml}"
      return 0
  if args[0]! == "kagree" then
    let data ← IO.FS.readFile args[1]!
    let stride := args[2]!.toNat!
    match parseAll data.toUTF8 with
    | none => return 1
    | some ts =>
      let mut n := 0
      let mut bad := 0
      let mut pbad := 0
      let t0 ← IO.monoMsNow
      for r in [0:15] do
        let ls := leaves (rootBox r) ts[r]!
        for k' in [0:ls.size / stride] do
          match ls.getD (k' * stride) (rootBox 0, Tree.fail) with
          | (b, Tree.dom c) =>
            if !(K.kDomOK (K.ofBox b) c) then
              bad := bad + 1
              if bad ≤ 5 then IO.println s!"dom reject root {r} code {c}"
            if !(K.pDomOK (K.ofBox b) c) then
              pbad := pbad + 1
              if pbad ≤ 5 then IO.println s!"packed dom reject root {r} code {c}"
          | (b, Tree.gap s w0 w1) =>
            n := n + 1
            if !(K.kGapOK (K.ofBox b) s w0 w1) then
              bad := bad + 1
              if bad ≤ 5 then IO.println s!"reject root {r} leaf {k' * stride} native {gapOK b b.polys s w0 w1}"
            if !(K.pGapOK (K.ofBox b) s w0 w1) then
              pbad := pbad + 1
              if pbad ≤ 5 then IO.println s!"packed reject root {r} leaf {k' * stride}"
          | _ => pure ()
      let t1 ← IO.monoMsNow
      IO.println s!"kGapOK: {n} gap leaves, {bad} rejected, packed {pbad} rejected, {t1 - t0} ms"
      return 0
  if args[0]! == "tiers" then
    let data ← IO.FS.readFile args[1]!
    let root := args[2]!.toNat!
    let stride := args[3]!.toNat!
    match parseAll data.toUTF8 with
    | none => return 1
    | some ts =>
      let ls := leaves (rootBox root) ts[root]!
      let mut t1 := 0
      let mut t2 := 0
      let mut t3 := 0
      let mut n := 0
      for k' in [0:ls.size / stride] do
        let k := k' * stride
        match ls.getD k (rootBox 0, Tree.fail) with
        | (b, Tree.gap s w0 w1) =>
          n := n + 1
          let bp := b.polys
          let g := gapData b bp vertexTab[s]! w0 w1
          for t in [0:90] do
            let T := vertexTab[t]!
            let quick := g.a0 - (T.x * g.e0.x + T.y * g.e0.y + T.z * g.e0.z) -
              (g.aS + Poly.dabs T.x * g.eS.x + Poly.dabs T.y * g.eS.y + Poly.dabs T.z * g.eS.z)
            if decide (g.err ≤ quick) then t1 := t1 + 1
            else if decide (g.err ≤ g.linBound T) then t2 := t2 + 1
            else t3 := t3 + 1
        | _ => pure ()
      IO.println s!"gap leaves {n}: per leaf quick {t1.toFloat / n.toFloat} lin {t2.toFloat / n.toFloat} full {t3.toFloat / n.toFloat}"
      return 0
  if args[0]! == "emit" then
    -- emit FILE ROOT STRIDE N : literal leaves for kernel probes
    let data ← IO.FS.readFile args[1]!
    let root := args[2]!.toNat!
    let stride := args[3]!.toNat!
    let n := args[4]!.toNat!
    match parseAll data.toUTF8 with
    | none => IO.println "parse failure"; return 1
    | some ts =>
      let ls := leaves (rootBox root) ts[root]!
      let mut i := 0
      let want := if args.length > 5 then args[5]! else "any"
      let ls := if want == "dom" then ls.filter (fun x => match x.2 with | .dom _ => true | _ => false)
        else if want == "gap" then ls.filter (fun x => match x.2 with | .gap .. => true | _ => false) else ls
      for k in [0:n] do
        let (b, t) := ls.getD ((k * stride) % ls.size) (rootBox 0, .fail)
        IO.println s!"example : leafOK {boxLit b} {treeLit t} = true := by decide +kernel"
        i := i + 1
      return 0
  let file := args[0]!
  let data ← IO.FS.readFile file
  let t0 ← IO.monoMsNow
  match args with
  | [_, rootStr] =>
    let root := rootStr.toNat!
    match parseTree data.toUTF8 200 0 with
    | none => IO.println "parse failure"; return 1
    | some (t, _) =>
      let t1 ← IO.monoMsNow
      IO.println s!"parsed {countLeaves t} leaves in {t1 - t0} ms"
      if args.length > 0 then profile root t
      let ok := checkTreePar 10 (rootBox root) t
      let t2 ← IO.monoMsNow
      IO.println s!"check: {ok} in {t2 - t1} ms"
      if !ok then
        let fs := failures (rootBox root) t
        IO.println s!"{fs.size} failing leaves"
        for (b, t) in fs.toList.take 10 do
          IO.println s!"  {showTree t} chart {b.chart} face {b.face} c {b.c.toArray.map (fun d => (d.m, d.e))} h {b.h.toArray.map (fun d => (d.m, d.e))}"
      return (if ok then 0 else 1)
  | _ =>
    let ok := checkAll data 12
    let t1 ← IO.monoMsNow
    IO.println s!"checkAll: {ok} in {t1 - t0} ms"
    return (if ok then 0 else 1)

