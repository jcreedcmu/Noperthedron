module

public import Cayley.Checker.Geometry

@[expose] public section

/-!
# The Cayley certificate checker

Mathlib-free. A certificate is a binary tree over the 15 root boxes (charts 1–3, and the
six blown-up faces of charts 0 and 4). Leaves are either *domain* leaves (one reduction
inequality fails on the whole box) or *gap* leaves (an inner vertex and a direction that
separates it from the outer shadow). See `cayley/DESIGN.md`.

Box coordinates `x₀..x₄` are `(u, v, r₀, r₁, r₂)` in charts 1–3 and `(u, v, s₀, s₁, ρ)` in
the blown-up charts, where `c` is the point of the cube face with free coordinates
`(s₀, s₁)` and `r = ρ c`.
-/

namespace Cayley

abbrev P := Poly 5

namespace P
@[inline] def add (a b : P) : P := Poly.add 5 a b
@[inline] def sub (a b : P) : P := Poly.sub 5 a b
@[inline] def mul (a b : P) : P := Poly.mul 5 a b
@[inline] def sm (c : QI) (a : P) : P := Poly.smul 5 c a
@[inline] def cst (c : QI) : P := Poly.const 5 c
@[inline] def zero : P := Poly.zero 5
@[inline] def lower (a : P) : QI := Poly.lower 5 a
end P

open P

def V3.dot (a b : V3 P) : P := add (add (mul a.x b.x) (mul a.y b.y)) (mul a.z b.z)

/-- `Σ aₖ · cₖ` for polynomial `a` and constant `c`. -/
def V3.dotC (a : V3 P) (c : V3 QI) : P := add (add (sm c.x a.x) (sm c.y a.y)) (sm c.z a.z)

def V3.cross (a b : V3 P) : V3 P :=
  ⟨sub (mul a.y b.z) (mul a.z b.y), sub (mul a.z b.x) (mul a.x b.z),
    sub (mul a.x b.y) (mul a.y b.x)⟩

def V3.const (c : V3 QI) : V3 P := ⟨cst c.x, cst c.y, cst c.z⟩

/-- Constant matrix times polynomial matrix. -/
def M3.mulCP (m : M3 QI) (p : M3 P) : M3 P :=
  let e (a0 a1 a2 : QI) (q0 q1 q2 : P) : P := add (add (sm a0 q0) (sm a1 q1)) (sm a2 q2)
  ⟨e m.a00 m.a01 m.a02 p.a00 p.a10 p.a20, e m.a00 m.a01 m.a02 p.a01 p.a11 p.a21,
    e m.a00 m.a01 m.a02 p.a02 p.a12 p.a22,
   e m.a10 m.a11 m.a12 p.a00 p.a10 p.a20, e m.a10 m.a11 m.a12 p.a01 p.a11 p.a21,
    e m.a10 m.a11 m.a12 p.a02 p.a12 p.a22,
   e m.a20 m.a21 m.a22 p.a00 p.a10 p.a20, e m.a20 m.a21 m.a22 p.a01 p.a11 p.a21,
    e m.a20 m.a21 m.a22 p.a02 p.a12 p.a22⟩

/-- Polynomial matrix times polynomial matrix. -/
def M3.mulPP (m p : M3 P) : M3 P :=
  let e (a0 a1 a2 q0 q1 q2 : P) : P := add (add (mul a0 q0) (mul a1 q1)) (mul a2 q2)
  ⟨e m.a00 m.a01 m.a02 p.a00 p.a10 p.a20, e m.a00 m.a01 m.a02 p.a01 p.a11 p.a21,
    e m.a00 m.a01 m.a02 p.a02 p.a12 p.a22,
   e m.a10 m.a11 m.a12 p.a00 p.a10 p.a20, e m.a10 m.a11 m.a12 p.a01 p.a11 p.a21,
    e m.a10 m.a11 m.a12 p.a02 p.a12 p.a22,
   e m.a20 m.a21 m.a22 p.a00 p.a10 p.a20, e m.a20 m.a21 m.a22 p.a01 p.a11 p.a21,
    e m.a20 m.a21 m.a22 p.a02 p.a12 p.a22⟩

def M3.transpose {α : Type} (m : M3 α) : M3 α :=
  ⟨m.a00, m.a10, m.a20, m.a01, m.a11, m.a21, m.a02, m.a12, m.a22⟩

/-- Constant matrix times constant matrix. -/
def M3.mulCC (m p : M3 QI) : M3 QI :=
  let e (a0 a1 a2 q0 q1 q2 : QI) : QI := a0 * q0 + a1 * q1 + a2 * q2
  ⟨e m.a00 m.a01 m.a02 p.a00 p.a10 p.a20, e m.a00 m.a01 m.a02 p.a01 p.a11 p.a21,
    e m.a00 m.a01 m.a02 p.a02 p.a12 p.a22,
   e m.a10 m.a11 m.a12 p.a00 p.a10 p.a20, e m.a10 m.a11 m.a12 p.a01 p.a11 p.a21,
    e m.a10 m.a11 m.a12 p.a02 p.a12 p.a22,
   e m.a20 m.a21 m.a22 p.a00 p.a10 p.a20, e m.a20 m.a21 m.a22 p.a01 p.a11 p.a21,
    e m.a20 m.a21 m.a22 p.a02 p.a12 p.a22⟩

def M3.mulVecC (p : M3 P) (v : V3 QI) : V3 P :=
  ⟨add (add (sm v.x p.a00) (sm v.y p.a01)) (sm v.z p.a02),
   add (add (sm v.x p.a10) (sm v.y p.a11)) (sm v.z p.a12),
   add (add (sm v.x p.a20) (sm v.y p.a21)) (sm v.z p.a22)⟩

def M3.mulCVec (m : M3 QI) (v : V3 P) : V3 P :=
  ⟨add (add (sm m.a00 v.x) (sm m.a01 v.y)) (sm m.a02 v.z),
   add (add (sm m.a10 v.x) (sm m.a11 v.y)) (sm m.a12 v.z),
   add (add (sm m.a20 v.x) (sm m.a21 v.y)) (sm m.a22 v.z)⟩

/-- `tr(Cᵀ X) = Σ C_ij X_ij`. -/
def M3.trTC (c : M3 QI) (x : M3 P) : P :=
  add (add (add (sm c.a00 x.a00) (sm c.a01 x.a01)) (add (sm c.a02 x.a02) (sm c.a10 x.a10)))
    (add (add (sm c.a11 x.a11) (sm c.a12 x.a12))
      (add (add (sm c.a20 x.a20) (sm c.a21 x.a21)) (sm c.a22 x.a22)))

/-- The Cayley numerator `N(x, y, z)` (same entries as `cayleyNumeratorMatrix`). -/
def cayNum (x y z : P) : M3 P :=
  let xx := mul x x
  let yy := mul y y
  let zz := mul z z
  let xy := mul x y
  let xz := mul x z
  let yz := mul y z
  let one := cst 1
  ⟨sub (sub (add one xx) yy) zz, sm 2 (sub xy z), sm 2 (add xz y),
   sm 2 (add xy z), sub (add (sub one xx) yy) zz, sm 2 (sub yz x),
   sm 2 (sub xz y), sm 2 (add yz x), add (sub (sub one xx) yy) zz⟩

structure Box where
  chart : Nat
  face : Nat
  c : Vector QI 5
  h : Vector QI 5

def Box.blowup (b : Box) : Bool := b.chart = 0 || b.chart = 4

def Box.split (b : Box) (d : Fin 5) : Box × Box :=
  let h' := QI.mk 1 1 * b.h[d]
  ({ b with c := b.c.set d (b.c[d] - h'), h := b.h.set d h' },
   { b with c := b.c.set d (b.c[d] + h'), h := b.h.set d h' })

def Box.var (b : Box) (i : Fin 5) : P := Poly.var 5 i b.c[i] b.h[i]

/-- The blow-up direction `c` on cube face `face` (axis `face / 2`, sign by parity). -/
def faceVec (face : Nat) (s0 s1 : P) : V3 P :=
  let sg : P := cst (if face % 2 = 0 then 1 else -1)
  match face / 2 with
  | 0 => ⟨sg, s0, s1⟩
  | 1 => ⟨s1, sg, s0⟩
  | _ => ⟨s0, s1, sg⟩

structure BoxPolys where
  /-- outer numerator `N(v, -u, 0)` -/
  no : M3 P
  /-- `M_j N(r)` -/
  mnr : M3 P
  dr : P
  /-- blow-up direction and radius (dummy outside charts 0, 4) -/
  cv : V3 P
  rho : P

def Box.cvec (b : Box) : V3 P := faceVec b.face (b.var 2) (b.var 3)

/-- The Cayley vector `r` as polynomials. -/
def Box.rvec (b : Box) : V3 P :=
  if b.blowup then
    let cv := b.cvec
    let rho := b.var 4
    ⟨mul rho cv.x, mul rho cv.y, mul rho cv.z⟩
  else ⟨b.var 2, b.var 3, b.var 4⟩

def Box.polys (b : Box) : BoxPolys :=
  let r := b.rvec
  { no := cayNum (b.var 1) (sm (-1) (b.var 0)) zero
    mnr := (chartM b.chart).mulCP (cayNum r.x r.y r.z)
    dr := add (add (add (cst 1) (mul r.x r.x)) (mul r.y r.y)) (mul r.z r.z)
    cv := b.cvec
    rho := b.var 4 }

/-- Data shared by all the outer-vertex tests of a gap leaf. -/
structure GapData where
  α : V3 P
  A : P
  E : V3 P
  a0 : QI
  aS : QI
  e0 : V3 QI
  eS : V3 QI
  err : QI
  /-- linear coefficients of `A` and of the `Eₖ` -/
  aL : List QI
  eL : V3 (List QI)
  /-- nonlinear slack `Σ|c| − |c₀| − Σ|linᵢ|` of `A` and of the `Eₖ` -/
  aN : QI
  eN : V3 QI

/-- `α = w₀ · (row 0 of N_o) + w₁ · (row 1 of N_o)`. -/
def alphaOf (bp : BoxPolys) (w0 w1 : Int) : V3 P :=
  let wd0 : QI := (w0 : QI)
  let wd1 : QI := (w1 : QI)
  ⟨add (sm wd0 bp.no.a00) (sm wd1 bp.no.a10),
    add (sm wd0 bp.no.a01) (sm wd1 bp.no.a11), add (sm wd0 bp.no.a02) (sm wd1 bp.no.a12)⟩

/-- The error allowance `128 κ ε (|w₀| + |w₁|)`. -/
def gapErr (chart : Nat) (w0 w1 : Int) : QI :=
  128 * chartK chart * errε * (Poly.dabs (w0 : QI) + Poly.dabs (w1 : QI))

/-- The slack `Σ|c| - |c₀|` of a polynomial. -/
def slack (q : P) : QI := Poly.absSum 5 q - Poly.dabs (Poly.constCoeff 5 q)

/-- The five linear coefficients. -/
def linCoeffs (q : P) : List QI := (List.range 5).map fun i => Poly.linCoeff 5 i q

/-- The nonlinear slack `Σ|c| − |c₀| − Σ|linᵢ|`. -/
def nlSlack (q : P) : QI :=
  slack q - (linCoeffs q).foldr (fun c acc => Poly.dabs c + acc) 0

def gapData (b : Box) (bp : BoxPolys) (S : V3 QI) (w0 w1 : Int) : GapData :=
  let α := alphaOf bp w0 w1
  let A := α.dot (bp.mnr.mulVecC S)
  let kdr := sm (chartK b.chart) bp.dr
  let E : V3 P := ⟨mul α.x kdr, mul α.y kdr, mul α.z kdr⟩
  { α, A, E
    a0 := Poly.constCoeff 5 A
    aS := slack A
    e0 := ⟨Poly.constCoeff 5 E.x, Poly.constCoeff 5 E.y, Poly.constCoeff 5 E.z⟩
    eS := ⟨slack E.x, slack E.y, slack E.z⟩
    err := gapErr b.chart w0 w1
    aL := linCoeffs A
    eL := ⟨linCoeffs E.x, linCoeffs E.y, linCoeffs E.z⟩
    aN := nlSlack A
    eN := ⟨nlSlack E.x, nlSlack E.y, nlSlack E.z⟩ }

/-- Lower bound of `A − Σ Tₖ Eₖ` with exact constant and linear terms. -/
def GapData.linBound (g : GapData) (T : V3 QI) : QI :=
  let c0 := g.a0 - (T.x * g.e0.x + T.y * g.e0.y + T.z * g.e0.z)
  let lin := List.zipWith (fun a e => a - e) g.aL
    (List.zipWith (fun a b => a + b) (List.zipWith (fun a b => a + b)
      (g.eL.x.map (T.x * ·)) (g.eL.y.map (T.y * ·))) (g.eL.z.map (T.z * ·)))
  let nl := g.aN + Poly.dabs T.x * g.eN.x + Poly.dabs T.y * g.eN.y + Poly.dabs T.z * g.eN.z
  c0 - lin.foldr (fun c acc => Poly.dabs c + acc) 0 - nl

/-- The test against outer vertex `T`: a quick constant-term test, else the full bound. -/
def GapData.outerOK (g : GapData) (T : V3 QI) : Bool :=
  let quick := g.a0 - (T.x * g.e0.x + T.y * g.e0.y + T.z * g.e0.z) -
    (g.aS + Poly.dabs T.x * g.eS.x + Poly.dabs T.y * g.eS.y + Poly.dabs T.z * g.eS.z)
  decide (g.err ≤ quick) || decide (g.err ≤ g.linBound T) ||
    decide (g.err ≤ lower (sub g.A (add (add (sm T.x g.E.x) (sm T.y g.E.y)) (sm T.z g.E.z))))

/-- The blown-up test for the paired vertex: `L = 2 α · M (c×S + ρ c×(c×S))`. -/
def pairedL (b : Box) (bp : BoxPolys) (α : V3 P) (S : V3 QI) : P :=
  let cs := bp.cv.cross (V3.const S)
  let ccs := bp.cv.cross cs
  let inner : V3 P := ⟨add cs.x (mul bp.rho ccs.x), add cs.y (mul bp.rho ccs.y),
    add cs.z (mul bp.rho ccs.z)⟩
  sm 2 (α.dot ((chartM b.chart).mulCVec inner))

/-- Gap leaf: inner vertex `s`, direction `(w0, w1)`. -/
def gapOK (b : Box) (bp : BoxPolys) (s : Nat) (w0 w1 : Int) : Bool :=
  if s < 90 then
    let S := vertexTab[s]!
    let g := gapData b bp S w0 w1
    let pr := if b.blowup then pairOf b.chart s else none
    let pairOK : Bool := match pr with
      | none => true
      | some _ => decide (g.err ≤ lower (pairedL b bp g.α S))
    (w0 != 0 || w1 != 0) && pairOK && (List.range 90).all fun t =>
      if pr = some t then true else g.outerOK vertexTab[t]!
  else false

/-- Disk test: `u² + v² > 1` on the whole box. -/
def domDisk (b : Box) : Bool :=
  let ulo := b.c[0] - b.h[0]
  let vlo := b.c[1] - b.h[1]
  decide (0 ≤ ulo) && decide (0 ≤ vlo) && decide (1 < ulo * ulo + vlo * vlo)

/-- Wedge test: `v > m u` on the whole box. -/
def domWedge (b : Box) : Bool :=
  let uhi := b.c[0] + b.h[0]
  let vlo := b.c[1] - b.h[1]
  decide (0 ≤ uhi) && decide (wedgeM * uhi < vlo)

/-- Chart test: chart `k` beats the box's chart `j`:
`tr(M_kᵀ M_j N) κ_j > tr(M_jᵀ M_j N) κ_k`. -/
def domChart (b : Box) (bp : BoxPolys) (k : Nat) : Bool :=
  let j := b.chart
  decide (0 < lower (sub (sm (chartK j) ((chartM k).trTC bp.mnr))
    (sm (chartK k) ((chartM j).trTC bp.mnr))))

/-- `D_o²`. -/
def Box.do2 (b : Box) : P :=
  let u := b.var 0
  let v := b.var 1
  let d := add (add (cst 1) (mul u u)) (mul v v)
  mul d d

/-- `N_oᵀ Z N_o = D_o² H`. -/
def BoxPolys.hn (bp : BoxPolys) : M3 P :=
  let z : M3 QI := ⟨-1, 0, 0, 0, -1, 0, 0, 0, 1⟩
  bp.no.transpose.mulPP (z.mulCP bp.no)

/-- The scaled orbit score of `X = H^e Q ĝ_g` for base `a` (`0` or `4`):
`κ₄ κ_j D_r D_o^{2e} (tr(B_aᵀ X) − [a = 4] δ)`. -/
def orbitSX (b : Box) (bp : BoxPolys) (e g a : Nat) : P :=
  let κj := chartK b.chart
  let κ4 := chartK 4
  let bg := (chartM a).mulCC groupTab[g]!.transpose
  let fa := if a = 4 then (1 : QI) else κ4
  let dsh := sm (biasδ * κ4 * κj) bp.dr
  if e = 0 then sub (sm fa (bg.trTC bp.mnr)) (if a = 4 then dsh else zero)
  else sub (sm fa (bg.trTC (bp.hn.mulPP bp.mnr))) (if a = 4 then mul b.do2 dsh else zero)

/-- The scaled scores `tr Q` and `tr(τᵀQ) − δ` of the box's own pose. -/
def orbitS0 (b : Box) (bp : BoxPolys) (e : Nat) : P :=
  let s0 := sm (chartK 4) ((chartM 0).trTC bp.mnr)
  if e = 0 then s0 else mul b.do2 s0

def orbitS4 (b : Box) (bp : BoxPolys) (e : Nat) : P :=
  let s4 := sub ((chartM 4).trTC bp.mnr) (sm (biasδ * chartK 4 * chartK b.chart) bp.dr)
  if e = 0 then s4 else mul b.do2 s4

def orbitErr (b : Box) (e : Nat) : QI :=
  (if e = 0 then 128 else 1024) * chartK 4 * chartK b.chart * errε

/-- Orbit test: the orbit element `H^e Q g` (base `a`) beats `Q` in the score `F`. -/
def domOrbit (b : Box) (bp : BoxPolys) (e g a : Nat) : Bool :=
  let sx := orbitSX b bp e g a
  decide (orbitErr b e < lower (sub sx (orbitS0 b bp e))) &&
    decide (orbitErr b e < lower (sub sx (orbitS4 b bp e)))

/-- Domain leaf `code`: some reduction inequality fails on the whole box. -/
def domainOK (b : Box) (bp : BoxPolys) (code : Nat) : Bool :=
  if code = 0 then domDisk b
  else if code = 1 then domWedge b
  else if code < 7 then domChart b bp (code - 2)
  else if code < 67 then
    let i := code - 7
    domOrbit b bp (i / 30) (i / 2 % 15) (if i % 2 = 0 then 0 else 4)
  else false

inductive Tree where
  | split (d : Fin 5) (l r : Tree)
  | dom (code : Nat)
  | gap (s : Nat) (w0 w1 : Int)
  | fail
deriving Inhabited

def leafOK (b : Box) : Tree → Bool
  | .dom code => domainOK b b.polys code
  | .gap s w0 w1 => gapOK b b.polys s w0 w1
  | _ => false

/-- Check a tree sequentially. -/
def checkTree (b : Box) : Tree → Bool
  | .split d l r =>
    let (bl, br) := b.split d
    checkTree bl l && checkTree br r
  | t => leafOK b t

/-- The subtrees at depth `d` (or leaves above it), with their boxes. -/
def frontier : Nat → Box → Tree → List (Box × Tree)
  | d + 1, b, .split dim l r =>
    let (bl, br) := b.split dim
    frontier d bl l ++ frontier d br r
  | _, b, t => [(b, t)]

/-- Check the subtrees at depth `d` in parallel (one task each). -/
def checkTreePar (d : Nat) (b : Box) (t : Tree) : Bool :=
  ((frontier d b t).map fun (b, t) => Task.spawn fun _ => checkTree b t).all (·.get)

/-! ## Roots -/

def dy (n : Int) (k : Nat) : QI := QI.mk n k

def rootBox (i : Nat) : Box :=
  let uv := [dy 1 1, dy 1 2]
  let huv := [dy 1 1, dy 1 2]
  if i < 3 then
    { chart := i + 1, face := 0, c := ⟨#[dy 1 1, dy 1 2, 0, 0, 0], rfl⟩,
      h := ⟨#[dy 1 1, dy 1 2, 1, 1, 1], rfl⟩ }
  else if i < 9 then
    { chart := 0, face := i - 3, c := ⟨#[dy 1 1, dy 1 2, 0, 0, dy 1 1], rfl⟩,
      h := ⟨#[dy 1 1, dy 1 2, 1, 1, dy 1 1], rfl⟩ }
  else
    let _ := (uv, huv)
    { chart := 4, face := i - 9, c := ⟨#[dy 1 1, dy 1 2, 0, 0, 1], rfl⟩,
      h := ⟨#[dy 1 1, dy 1 2, 1, 1, 1], rfl⟩ }

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
def parseTree (s : ByteArray) : Nat → Nat → Option (Tree × Nat)
  | 0, _ => none
  | fuel + 1, i =>
    if h : i < s.size then
      let c := s[i]
      if c = 83 then -- 'S'
        let (d, j) := readInt s (i + 1)
        if hd : 0 ≤ d ∧ d < 5 then
          match parseTree s fuel (j + 1) with
          | none => none
          | some (l, k) =>
            match parseTree s fuel k with
            | none => none
            | some (r, m) => some (.split ⟨d.toNat, by omega⟩ l r, m)
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

def parseAll (s : ByteArray) : Option (Array Tree) := Id.run do
  let mut i := 0
  let mut out : Array Tree := #[]
  for _ in [0:15] do
    match parseTree s 200 i with
    | none => return none
    | some (t, j) =>
      out := out.push t
      i := j
  if i < s.size then return none
  return some out

/-- The whole check: parse the 15 trees and check each against its root box. -/
def checkAll (data : String) (par : Nat) : Bool :=
  match parseAll data.toUTF8 with
  | none => false
  | some ts =>
    let jobs := ((List.range 15).map fun i => frontier par (rootBox i) (ts[i]!)).flatten
    let tasks := jobs.map fun (b, t) => Task.spawn fun _ => checkTree b t
    decide (ts.size = 15) && tasks.all (·.get)

end Cayley

end
