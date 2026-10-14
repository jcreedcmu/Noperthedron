module

public import Cayley.Checker.KGap

@[expose] public section

/-!
# Kronecker-packed kernel checker

A polynomial in `t₀, …, t₄` with every exponent `≤ 2` is stored as the integer obtained by
evaluating it at `tᵢ = 2^(W·3ⁱ)`. This is a ring homomorphism, so polynomial arithmetic is a
handful of big-integer operations, which the kernel evaluates with GMP. Coefficient statistics
(constant term, sums of absolute values over a set of monomials) are read off with masks:
after adding the offset `2^(W-1)` to every slot, slot `j` holds `coeff_j + 2^(W-1)`, its top
bit is the sign, and a horizontal sum of slots is a remainder modulo `2^W - 1`.
-/

namespace Cayley.K

/-- Slot width in bits. -/
def PW : Nat := 400

/-- `2^PW - 1`. -/
def pM : Nat := 2 ^ PW - 1

/-! ### Layouts

Layout `L3`: `tᵢ = 2^(PW·3ⁱ)` (243 slots, exponents `≤ 2`). Layout `L5`: `t₀ = 2^PW`,
`t₁ = 2^(5PW)`, `t₂, t₃, t₄ = 2^(25PW), 2^(75PW), 2^(225PW)` (675 slots, exponents `≤ 4` in
`t₀, t₁` and `≤ 2` in the others). -/

/-- The variable `tᵢ` of layout `L3`. -/
def pX (i : Nat) : Int := ((2 ^ (PW * 3 ^ i) : Nat) : Int)

/-- The variable `tᵢ` of layout `L5`. -/
def qX (i : Nat) : Int := ((2 ^ (PW * (if i = 0 then 1 else if i = 1 then 5 else 25 * 3 ^ (i - 2))) : Nat) : Int)

/-- `1 + y + y²` and `1 + y²`. -/
def geo3 (y : Nat) : Nat := Nat.add (Nat.add 1 y) (Nat.mul y y)
def ev3 (y : Nat) : Nat := Nat.add 1 (Nat.mul y y)
/-- `1 + y + y² + y³ + y⁴` and `1 + y² + y⁴`. -/
def geo5 (y : Nat) : Nat := Nat.add (Nat.mul (Nat.mul y y) (geo3 y)) (Nat.add 1 y)
def ev5 (y : Nat) : Nat := Nat.add 1 (Nat.mul (Nat.mul y y) (ev3 y))

/-- Slot indicators (`Σ 2^(PW j)` over all slots, and over the all-even monomials). -/
def onesL3 : Nat :=
  Nat.mul (Nat.mul (Nat.mul (Nat.mul (geo3 (pX 0).toNat) (geo3 (pX 1).toNat)) (geo3 (pX 2).toNat))
    (geo3 (pX 3).toNat)) (geo3 (pX 4).toNat)
def evensL3 : Nat :=
  Nat.mul (Nat.mul (Nat.mul (Nat.mul (ev3 (pX 0).toNat) (ev3 (pX 1).toNat)) (ev3 (pX 2).toNat))
    (ev3 (pX 3).toNat)) (ev3 (pX 4).toNat)
def onesL5 : Nat :=
  Nat.mul (Nat.mul (Nat.mul (Nat.mul (geo5 (qX 0).toNat) (geo5 (qX 1).toNat)) (geo3 (qX 2).toNat))
    (geo3 (qX 3).toNat)) (geo3 (qX 4).toNat)
def evensL5 : Nat :=
  Nat.mul (Nat.mul (Nat.mul (Nat.mul (ev5 (qX 0).toNat) (ev5 (qX 1).toNat)) (ev3 (qX 2).toNat))
    (ev3 (qX 3).toNat)) (ev3 (qX 4).toNat)

/-- Statistics of a packed polynomial `P`: constant term, `slack` with
`P ≥ c0 − slack` on `[-1,1]⁵` (even monomials only count when negative), and `abs`
with `|P − c0| ≤ abs`. -/
structure PStats where
  c0 : Int
  slack : Nat
  abs : Nat

/-- Positive and negative parts of the slots of `N = P + offset`. -/
@[inline] def pParts (ones N : Nat) : Nat × Nat :=
  let off : Nat := Nat.mul (2 ^ (PW - 1)) ones
  let pm : Nat := Nat.mul pM (Nat.land (Nat.shiftRight N (PW - 1)) ones)
  let nm : Nat := Nat.sub (Nat.mul pM ones) pm
  (Nat.sub (Nat.land N pm) (Nat.land off pm), Nat.sub (Nat.land off nm) (Nat.land N nm))

def pStatsL (ones evens : Nat) (P : Int) : PStats :=
  let N : Nat := Int.toNat (Int.add P (Nat.mul (2 ^ (PW - 1)) ones : Nat))
  let (pos, neg) := pParts ones N
  let ab : Nat := Nat.add pos neg
  { c0 := Int.subNatNat (Nat.land N pM) (2 ^ (PW - 1))
    slack := Nat.mod (Nat.add (Nat.land ab (Nat.mul pM (Nat.sub ones evens)))
      (Nat.land neg (Nat.mul pM (Nat.sub evens 1)))) pM
    abs := Nat.mod (Nat.land ab (Nat.sub (Nat.mul pM ones) pM)) pM }

/-- Lower bound of a packed polynomial on `[-1,1]⁵`. -/
def pLowerL (ones evens : Nat) (P : Int) : Int :=
  let N : Nat := Int.toNat (Int.add P (Nat.mul (2 ^ (PW - 1)) ones : Nat))
  let (pos, neg) := pParts ones N
  Int.subNatNat (Nat.land N pM)
    (Nat.add (2 ^ (PW - 1)) (Nat.mod (Nat.add (Nat.land pos (Nat.mul pM (Nat.sub ones evens)))
      (Nat.land neg (Nat.sub (Nat.mul pM ones) pM))) pM))

def pStats (P : Int) : PStats := pStatsL onesL3 evensL3 P
def pLower (P : Int) : Int := pLowerL onesL3 evensL3 P
def qLower (P : Int) : Int := pLowerL onesL5 evensL5 P

/-! ### Bernstein coefficients (layout `L3`)

On `[-1,1]` the quadratic Bernstein coefficients of `a₀ + a₁t + a₂t²` are
`(a₀ − a₁ + a₂, a₀ − a₂, a₀ + a₁ + a₂)`; `baxis i` applies this along variable `i` to every
slot of a packed polynomial, and a polynomial is at least its least Bernstein coefficient. -/

/-- Slot indicator of the slots whose digit `i` is `0`. -/
def zL3 (i : Nat) : Nat := Nat.div onesL3 (geo3 (pX i).toNat)

/-- The Bernstein transform along variable `i` of a packed polynomial. -/
def baxis (i : Nat) (P : Int) : Int :=
  let z := zL3 i
  let sh := Nat.mul PW (3 ^ i)
  let sh2 := Nat.add sh sh
  let off : Nat := Nat.mul (2 ^ (PW - 1)) z
  let N : Nat := Int.toNat (Int.add P (Nat.mul (2 ^ (PW - 1)) onesL3 : Nat))
  let mz : Nat := Nat.mul pM z
  let n0 : Int := Int.subNatNat (Nat.land N mz) off
  let n1 : Int := Int.subNatNat (Nat.shiftRight (Nat.land N (Nat.shiftLeft mz sh)) sh) off
  let n2 : Int := Int.subNatNat (Nat.shiftRight (Nat.land N (Nat.shiftLeft mz sh2)) sh2) off
  Int.add (Int.add (Int.add (Int.sub n0 n1) n2) (Int.mul ((2 ^ sh : Nat) : Int) (Int.sub n0 n2)))
    (Int.mul ((2 ^ sh2 : Nat) : Int) (Int.add (Int.add n0 n1) n2))

/-- The Bernstein coefficients of a packed polynomial. -/
def bern3 (P : Int) : Int := baxis 4 (baxis 3 (baxis 2 (baxis 1 (baxis 0 P))))

/-- Every Bernstein coefficient of the packed polynomial `P` is at least `m`. -/
def bernGE (P m : Int) : Bool :=
  let N : Nat := Int.toNat (Int.add (Int.sub (bern3 P) (Int.mul (onesL3 : Int) m))
    (Nat.mul (2 ^ (PW - 1)) onesL3 : Nat))
  Nat.blt m.natAbs (2 ^ 390) && Nat.beq (Nat.land (Nat.shiftRight N (PW - 1)) onesL3) onesL3

/-- The per-box polynomials of a gap leaf, over any arithmetic: `α₀, α₁, α₂` (outer rows,
weighted by `w`), `β = M N(r) S`, `κD`, and the paired inner vector `L` (blown-up charts). -/
structure GData (R : Type) where
  a0 : R
  a1 : R
  a2 : R
  b0 : R
  b1 : R
  b2 : R
  kd : R
  l0 : R
  l1 : R
  l2 : R

/-- `M_j v`; the Klein charts are sign flips. -/
def gChart {R : Type} (sub mul : R → R → R) (c : Int → R) (add : R → R → R) (chart : Nat)
    (y0 y1 y2 : R) : R × R × R :=
  match chart with
  | 0 => (y0, y1, y2)
  | 1 => (y0, sub (c 0) y1, sub (c 0) y2)
  | 2 => (sub (c 0) y0, y1, sub (c 0) y2)
  | 3 => (sub (c 0) y0, sub (c 0) y1, y2)
  | _ =>
    let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := chartMI 4
    (add (add (mul (c m00) y0) (mul (c m01) y1)) (mul (c m02) y2),
     add (add (mul (c m10) y0) (mul (c m11) y1)) (mul (c m12) y2),
     add (add (mul (c m20) y0) (mul (c m21) y1)) (mul (c m22) y2))

/-- The blow-up direction on cube face `face`, with sign entry `sg`. -/
def gFace {R : Type} (face : Nat) (sg s0 s1 : R) : R × R × R :=
  if face / 2 = 0 then (sg, s0, s1) else if face / 2 = 1 then (s1, sg, s0) else (s0, s1, sg)

/-- The gap-leaf polynomials, generic in the arithmetic (`x i` is the variable `tᵢ`). -/
def gapGen {R : Type} (add sub mul : R → R → R) (c : Int → R) (x : Fin 5 → R)
    (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : GData R :=
  let U := c (p2 b.K)
  let U2 := mul U U
  let u := add (c (b.c.getD 0 0)) (mul (c (b.h.getD 0 0)) (x 0))
  let v := add (c (b.c.getD 1 0)) (mul (c (b.h.getD 1 0)) (x 1))
  let uu := mul u u
  let vv := mul v v
  let uv := mul u v
  -- rows 0, 1 of N(v, -u, 0) · U²
  let n00 := sub (add U2 vv) uu
  let n01 := mul (c (-2)) uv
  let n02 := mul (mul (c (-2)) U) u
  let n11 := add (sub U2 vv) uu
  let n12 := mul (mul (c (-2)) U) v
  let a0 := add (mul (c w0) n00) (mul (c w1) n01)
  let a1 := add (mul (c w0) n01) (mul (c w1) n11)
  let a2 := add (mul (c w0) n02) (mul (c w1) n12)
  let sx := c S.1
  let sy := c S.2.1
  let sz := c S.2.2
  let κ := c (chartKI b.chart)
  if b.chart = 0 ∨ b.chart = 4 then
    let sg : R := if b.face % 2 = 0 then U else sub (c 0) U
    let s0 := add (c (b.c.getD 2 0)) (mul (c (b.h.getD 2 0)) (x 2))
    let s1 := add (c (b.c.getD 3 0)) (mul (c (b.h.getD 3 0)) (x 3))
    let (cx, cy, cz) : R × R × R := gFace b.face sg s0 s1
    let ρ := add (c (b.c.getD 4 0)) (mul (c (b.h.getD 4 0)) (x 4))
    let ρ2 := mul ρ ρ
    let c2 := add (add (mul cx cx) (mul cy cy)) (mul cz cz)
    let cS := add (add (mul sx cx) (mul sy cy)) (mul sz cz)
    let x0 := sub (mul sz cy) (mul sy cz)
    let x1 := sub (mul sx cz) (mul sz cx)
    let x2 := sub (mul sy cx) (mul sx cy)
    let U4 := mul U2 U2
    -- N(ρc)S = S U⁴ + (2 c(c·S) − |c|² S) ρ² + 2U² (c×S) ρ
    let nk (s cc xx : R) : R :=
      add (add (mul s U4) (mul (sub (mul (mul (c 2) cc) cS) (mul s c2)) ρ2))
        (mul (mul (mul (c 2) U2) xx) ρ)
    let (b0, b1, b2) := gChart sub mul c add b.chart (nk sx cx x0) (nk sy cy x1) (nk sz cz x2)
    let d := add U4 (mul c2 ρ2)
    -- paired inner vector U² (c×S) + ρ c×(c×S), over U³
    let k0 := sub (mul cy x2) (mul cz x1)
    let k1 := sub (mul cz x0) (mul cx x2)
    let k2 := sub (mul cx x1) (mul cy x0)
    let (l0, l1, l2) := gChart sub mul c add b.chart (add (mul U2 x0) (mul k0 ρ))
      (add (mul U2 x1) (mul k1 ρ)) (add (mul U2 x2) (mul k2 ρ))
    { a0, a1, a2, b0, b1, b2, kd := mul κ d, l0, l1, l2 }
  else
    let r0 := add (c (b.c.getD 2 0)) (mul (c (b.h.getD 2 0)) (x 2))
    let r1 := add (c (b.c.getD 3 0)) (mul (c (b.h.getD 3 0)) (x 3))
    let r2 := add (c (b.c.getD 4 0)) (mul (c (b.h.getD 4 0)) (x 4))
    let r2s := add (add (mul r0 r0) (mul r1 r1)) (mul r2 r2)
    let rS := add (add (mul sx r0) (mul sy r1)) (mul sz r2)
    let base := sub U2 r2s
    let nk (s r xx : R) : R :=
      add (add (mul s base) (mul (mul (c 2) r) rS)) (mul (mul (c 2) U) xx)
    let (b0, b1, b2) := gChart sub mul c add b.chart
      (nk sx r0 (sub (mul sz r1) (mul sy r2)))
      (nk sy r1 (sub (mul sx r2) (mul sz r0)))
      (nk sz r2 (sub (mul sy r0) (mul sx r1)))
    { a0, a1, a2, b0, b1, b2, kd := mul κ (add U2 r2s), l0 := c 0, l1 := c 0, l2 := c 0 }

/-- The gap-leaf data in packed integers. -/
def pGapData (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : GData Int :=
  gapGen Int.add Int.sub Int.mul (fun z => z) (fun i => pX i.val) b S w0 w1

/-- Coefficient-norm bounds of the gap-leaf polynomials (the `Nat` instance of `gapGen`). -/
def gapNrm (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : GData Nat :=
  gapGen Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1) b S w0 w1

/-- The packed polynomials stay decodable: every polynomial the gap test decodes has
coefficient norm below `2^390` (room for the Bernstein transform) (outer vertices have coordinates below `2^161`). -/
def gapNrmOK (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : Bool :=
  let nb := gapNrm b S w0 w1
  let nA := Nat.add (Nat.add (Nat.mul nb.a0 nb.b0) (Nat.mul nb.a1 nb.b1)) (Nat.mul nb.a2 nb.b2)
  let nX := Nat.mul (2 ^ 161) (Nat.add (Nat.add nb.a0 nb.a1) nb.a2)
  Nat.blt (Nat.add nA (Nat.mul nX nb.kd)) (2 ^ 390) &&
    Nat.blt (Nat.add (Nat.add (Nat.mul nb.a0 nb.l0) (Nat.mul nb.a1 nb.l1)) (Nat.mul nb.a2 nb.l2)) (2 ^ 390)

/-- Scale exponents of `A` and of `L` beyond `2^160`. -/
def gapSc (b : KBox) : Nat := if b.chart = 0 ∨ b.chart = 4 then 6 * b.K else 4 * b.K
def gapScL (b : KBox) : Nat := 5 * b.K

/-! ### The gap leaf -/

/-- The error allowance of a gap leaf (for `A`) and of the paired test (for `L`). -/
def gErr (b : KBox) (w0 w1 : Int) : Int :=
  128 * chartKI b.chart * ((w0.natAbs : Int) + w1.natAbs) * p2 (gapSc b + 100)
def gErrL (b : KBox) (w0 w1 : Int) : Int :=
  128 * chartKI b.chart * ((w0.natAbs : Int) + w1.natAbs) * p2 (gapScL b + 100)

/-- `A = Σ αₖ βₖ`, `L = Σ αₖ Lₖ`, `Eₖ = αₖ κD`, `F_T = A − (Σ Tₖ αₖ) κD`. -/
def gA (g : GData Int) : Int := Int.add (Int.add (Int.mul g.a0 g.b0) (Int.mul g.a1 g.b1)) (Int.mul g.a2 g.b2)
def gL (g : GData Int) : Int := Int.add (Int.add (Int.mul g.a0 g.l0) (Int.mul g.a1 g.l1)) (Int.mul g.a2 g.l2)
def gF (g : GData Int) (tx ty tz : Int) : Int :=
  Int.sub (gA g) (Int.mul (Int.add (Int.add (Int.mul tx g.a0) (Int.mul ty g.a1)) (Int.mul tz g.a2)) g.kd)

/-- The exact test against outer vertex `T`, and the paired test. -/
def fullOK (b : KBox) (S : Int × Int × Int) (w0 w1 tx ty tz : Int) : Bool :=
  decide (gErr b w0 w1 ≤ pLower (gF (pGapData b S w0 w1) tx ty tz)) ||
    bernGE (gF (pGapData b S w0 w1) tx ty tz) (gErr b w0 w1)
def pairOK (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : Bool :=
  decide (gErrL b w0 w1 ≤ 2 * pLower (gL (pGapData b S w0 w1))) ||
    bernGE (Int.mul 2 (gL (pGapData b S w0 w1))) (gErrL b w0 w1)

/-- The paired vertex of inner vertex `s` (blown-up charts). -/
def gPair (b : KBox) (s : Nat) : Option Nat := if b.chart = 0 ∨ b.chart = 4 then kPair b.chart s else none

/-- The test of outer vertex `t` after the packed quick test. -/
def vtestG (b : KBox) (s : Nat) (w0 w1 : Int) (t : Nat) (tx ty tz : Int) : Bool :=
  if gPair b s = some t then
    pairOK b (vtxI.getD s (0, 0, 0)) w0 w1 ||
      (!decide (b.c.getD 4 0 - b.h.getD 4 0 ≤ 0) && fullOK b (vtxI.getD s (0, 0, 0)) w0 w1 tx ty tz)
  else fullOK b (vtxI.getD s (0, 0, 0)) w0 w1 tx ty tz

/-- The quick test's constant part `c₀(A) − slack(A) − err`, and the statistics of `Eₖ`. -/
def quickQ (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : Int :=
  let sA := pStats (gA (pGapData b S w0 w1))
  sA.c0 - sA.slack - gErr b w0 w1
def quickE (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : PStats × PStats × PStats :=
  let g := pGapData b S w0 w1
  (pStats (Int.mul g.a0 g.kd), pStats (Int.mul g.a1 g.kd), pStats (Int.mul g.a2 g.kd))

/-- The packed quick-test number: slot `t` is `2^639 + quick_T` when the packing bounds hold. -/
def quickV (C e00 e01 e02 : Int) (n0 n1 n2 : Nat) : Nat :=
  let tab (e : Int) (tn tp : Nat) : Nat := Nat.mul (if 0 ≤ e then tn else tp) e.natAbs
  Nat.add (Nat.add (Nat.add (Nat.mul onesT C.toNat) (tab e00 tnx tpx))
    (Nat.add (tab e01 tny tpy) (tab e02 tnz tpz)))
    (Nat.add (Nat.mul tax n0) (Nat.add (Nat.mul tay n1) (Nat.mul taz n2)))

/-- Packed kernel gap leaf. -/
def pGapOK (b : KBox) (s : Nat) (w0 w1 : Int) : Bool :=
  if s < 90 then
    let S := vtxI.getD s (0, 0, 0)
    let (E0, E1, E2) := quickE b S w0 w1
    let tot : Int := ((E0.c0.natAbs : Int) + E1.c0.natAbs + E2.c0.natAbs) +
      ((E0.abs : Int) + E1.abs + E2.abs)
    let C : Int := p2 639 + quickQ b S w0 w1 - p2 170 * tot
    let packOK : Bool := decide (0 ≤ C) && decide (C + 2 * p2 170 * tot < p2 640)
    (w0 != 0 || w1 != 0) && gapNrmOK b S w0 w1 &&
      if packOK then
        vtxSplit (fun t tx ty tz _ _ _ => vtestG b s w0 w1 t tx ty tz) 8 0 90
          (Nat.xor signT (Nat.land (quickV C E0.c0 E1.c0 E2.c0 E0.abs E1.abs E2.abs) signT))
      else vtxIdx.all fun (t, (tx, ty, tz), _) => vtestG b s w0 w1 t tx ty tz
  else false

/-! ### Domain leaves -/

abbrev I9 := Int × Int × Int × Int × Int × Int × Int × Int × Int

/-- A 3×3 matrix of polynomials and a scalar. -/
structure NM (R : Type) where
  n00 : R
  n01 : R
  n02 : R
  n10 : R
  n11 : R
  n12 : R
  n20 : R
  n21 : R
  n22 : R
  d : R

/-- The Cayley numerator `N(r)` and the denominator `D` of a box, generic in the arithmetic. -/
def numGen {R : Type} (add sub mul : R → R → R) (c : Int → R) (x : Fin 5 → R) (b : KBox) : NM R :=
  let U := c (p2 b.K)
  let U2 := mul U U
  if b.chart = 0 ∨ b.chart = 4 then
    let sg : R := if b.face % 2 = 0 then U else sub (c 0) U
    let s0 := add (c (b.c.getD 2 0)) (mul (c (b.h.getD 2 0)) (x 2))
    let s1 := add (c (b.c.getD 3 0)) (mul (c (b.h.getD 3 0)) (x 3))
    let (cx, cy, cz) : R × R × R := gFace b.face sg s0 s1
    let ρ := add (c (b.c.getD 4 0)) (mul (c (b.h.getD 4 0)) (x 4))
    let ρ2 := mul ρ ρ
    let c2 := add (add (mul cx cx) (mul cy cy)) (mul cz cz)
    let U4 := mul U2 U2
    let dg (ca : R) : R := add U4 (mul (sub (mul (mul (c 2) ca) ca) c2) ρ2)
    let od (ca cb cc : R) (sgn : Int) : R :=
      add (mul (mul (mul (c 2) ca) cb) ρ2) (mul (mul (c (sgn * 2)) U2) (mul cc ρ))
    ⟨dg cx, od cx cy cz (-1), od cx cz cy 1,
      od cy cx cz 1, dg cy, od cy cz cx (-1),
      od cz cx cy (-1), od cz cy cx 1, dg cz, add U4 (mul c2 ρ2)⟩
  else
    let r0 := add (c (b.c.getD 2 0)) (mul (c (b.h.getD 2 0)) (x 2))
    let r1 := add (c (b.c.getD 3 0)) (mul (c (b.h.getD 3 0)) (x 3))
    let r2 := add (c (b.c.getD 4 0)) (mul (c (b.h.getD 4 0)) (x 4))
    let r2s := add (add (mul r0 r0) (mul r1 r1)) (mul r2 r2)
    let base := sub U2 r2s
    let dg (ra : R) : R := add base (mul (mul (c 2) ra) ra)
    let od (ra rb rc : R) (sgn : Int) : R :=
      add (mul (mul (c 2) ra) rb) (mul (mul (c (sgn * 2)) U) rc)
    ⟨dg r0, od r0 r1 r2 (-1), od r0 r2 r1 1,
      od r1 r0 r2 1, dg r1, od r1 r2 r0 (-1),
      od r2 r0 r1 (-1), od r2 r1 r0 1, dg r2, add U2 r2s⟩

/-- The scale `R²` of `N` (`U⁴` blown up, `U²` plain). -/
def numSc (b : KBox) : Int :=
  if b.chart = 0 ∨ b.chart = 4 then p2 b.K * p2 b.K * (p2 b.K * p2 b.K) else p2 b.K * p2 b.K

/-- `tr(Xᵀ N) = Σ X_ab N_ab` for an integer matrix `X`. -/
def trGen {R : Type} (add mul : R → R → R) (c : Int → R) (X : I9) (N : NM R) : R :=
  let (x00, x01, x02, x10, x11, x12, x20, x21, x22) := X
  add (add (add (add (add (add (add (add (mul (c x00) N.n00) (mul (c x01) N.n01))
    (mul (c x02) N.n02)) (mul (c x10) N.n10)) (mul (c x11) N.n11)) (mul (c x12) N.n12))
    (mul (c x20) N.n20)) (mul (c x21) N.n21)) (mul (c x22) N.n22)

/-- The chart-test polynomial `κⱼ tr((Mⱼᵀ M_k)ᵀ N) − κ_k tr((Mⱼᵀ Mⱼ)ᵀ N)`. -/
def chartGen {R : Type} (add sub mul : R → R → R) (c : Int → R) (x : Fin 5 → R) (b : KBox)
    (k : Nat) : R :=
  let N := numGen add sub mul c x b
  let Mj := chartMI b.chart
  sub (mul (c (chartKI b.chart)) (trGen add mul c (mtm Mj (chartMI k)) N))
    (mul (c (chartKI k)) (trGen add mul c (mtm Mj Mj) N))

/-- `C = M_a · 2^80 R̂z(g)ᵀ` (integer). -/
def orbC (g a : Nat) : I9 :=
  let cg := (cosTab.getD g 0).m
  let sg := (sinTab.getD g 0).m
  mmI (chartMI a) (cg, sg, 0, -sg, cg, 0, 0, 0, p2 80)

/-- `M N` for an integer matrix `M` (the scalar is kept). -/
def m3 {R : Type} (add mul : R → R → R) (c : Int → R) (M : I9) (N : NM R) : NM R :=
  let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := M
  let e (a0 a1 a2 : Int) (x0 x1 x2 : R) : R := add (add (mul (c a0) x0) (mul (c a1) x1)) (mul (c a2) x2)
  ⟨e m00 m01 m02 N.n00 N.n10 N.n20, e m00 m01 m02 N.n01 N.n11 N.n21, e m00 m01 m02 N.n02 N.n12 N.n22,
   e m10 m11 m12 N.n00 N.n10 N.n20, e m10 m11 m12 N.n01 N.n11 N.n21, e m10 m11 m12 N.n02 N.n12 N.n22,
   e m20 m21 m22 N.n00 N.n10 N.n20, e m20 m21 m22 N.n01 N.n11 N.n21, e m20 m21 m22 N.n02 N.n12 N.n22,
   N.d⟩

/-- Transpose. -/
def m3t {R : Type} (N : NM R) : NM R := ⟨N.n00, N.n10, N.n20, N.n01, N.n11, N.n21, N.n02, N.n12, N.n22, N.d⟩

/-- `Σ_ab H_ab W_ab`. -/
def frob {R : Type} (add mul : R → R → R) (H W : NM R) : R :=
  add (add (add (add (add (add (add (add (mul H.n00 W.n00) (mul H.n01 W.n01)) (mul H.n02 W.n02))
    (mul H.n10 W.n10)) (mul H.n11 W.n11)) (mul H.n12 W.n12)) (mul H.n20 W.n20)) (mul H.n21 W.n21))
    (mul H.n22 W.n22)

/-- `H = N_oᵀ diag(-1,-1,1) N_o` for the outer numerator `N_o = N(v, -u, 0)·U²`. -/
def hGen {R : Type} (add sub mul : R → R → R) (c : Int → R) (u v U : R) : NM R :=
  let U2 := mul U U
  let uu := mul u u
  let vv := mul v v
  let n00 := sub (add U2 vv) uu
  let n01 := mul (c (-2)) (mul u v)
  let n02 := mul (mul (c (-2)) U) u
  let n11 := add (sub U2 vv) uu
  let n12 := mul (mul (c (-2)) U) v
  let n20 := mul (mul (c 2) U) u
  let n21 := mul (mul (c 2) U) v
  let n22 := sub (sub U2 vv) uu
  let hab (x0 y0 x1 y1 x2 y2 : R) : R := sub (sub (mul x2 y2) (mul x0 y0)) (mul x1 y1)
  let h01 := hab n00 n01 n01 n11 n20 n21
  let h02 := hab n00 n02 n01 n12 n20 n22
  let h12 := hab n01 n02 n11 n12 n21 n22
  ⟨hab n00 n00 n01 n01 n20 n20, h01, h02, h01, hab n01 n01 n11 n11 n21 n21, h12, h02, h12,
    hab n02 n02 n12 n12 n22 n22, c 0⟩

/-- The two orbit-test polynomials (score of the orbit element minus the scores of `Q`). -/
def orbGen {R : Type} (add sub mul : R → R → R) (c : Int → R) (x : Fin 5 → R) (b : KBox)
    (e g a : Nat) : R × R :=
  let N := numGen add sub mul c x b
  let Mj := chartMI b.chart
  let κj := chartKI b.chart
  let κ4 := kappaTau
  let C := orbC g a
  let fa : Int := if a = 4 then 1 else κ4
  let tr0 := trGen add mul c (mtm Mj (chartMI 0)) N
  let tr4 := trGen add mul c (mtm Mj (chartMI 4)) N
  let dsh := mul (c (κ4 * κj * p2 77)) N.d
  if e = 0 then
    let sx := mul (c fa) (trGen add mul c (mtm Mj C) N)
    let sx := if a = 4 then sub sx dsh else sx
    (sub sx (mul (c (κ4 * p2 80)) tr0), sub sx (sub (mul (c (p2 80)) tr4) dsh))
  else
    let U := c (p2 b.K)
    let U2 := mul U U
    let u := add (c (b.c.getD 0 0)) (mul (c (b.h.getD 0 0)) (x 0))
    let v := add (c (b.c.getD 1 0)) (mul (c (b.h.getD 1 0)) (x 1))
    let uu := mul u u
    let vv := mul v v
    let T := mul (c fa) (frob add mul (hGen add sub mul c u v U)
      (m3 add mul c C (m3t (m3 add mul c Mj N))))
    let dO := add (add U2 uu) vv
    let do2 := mul dO dO
    let ash := if a = 4 then dsh else c 0
    (sub T (mul do2 (add ash (mul (c (κ4 * p2 80)) tr0))),
      sub T (mul do2 (add ash (sub (mul (c (p2 80)) tr4) dsh))))

/-- The variables of layout `L5`. -/
def qXv (i : Fin 5) : Int := qX i.val

/-- The norm guard of a domain polynomial (the `Nat` instance). -/
def chartNrmOK (b : KBox) (k : Nat) : Bool :=
  Nat.blt (chartGen Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1) b k) (2 ^ 399)
def orbNrmOK (b : KBox) (e g a : Nat) : Bool :=
  let P := orbGen Nat.add Nat.add Nat.mul Int.natAbs (fun _ => 1) b e g a
  Nat.blt P.1 (2 ^ 399) && Nat.blt P.2 (2 ^ 399)

/-- Kernel chart test: chart `k` beats the box's chart `j` on the whole box. -/
def pChartOK (b : KBox) (k : Nat) : Bool :=
  chartNrmOK b k &&
    decide (0 < pLower (chartGen Int.add Int.sub Int.mul (fun z => z) (fun i => pX i.val) b k))

/-- The orbit-test error allowance. -/
def orbErr (b : KBox) (e : Nat) : Int :=
  if e = 0 then 128 * kappaTau * chartKI b.chart * numSc b * p2 20
  else 1024 * kappaTau * chartKI b.chart * (p2 b.K * p2 b.K * (p2 b.K * p2 b.K)) * numSc b * p2 20

/-- Kernel orbit test: the orbit element `H^e Q ĝ_g` (score base `a`) beats `Q`. -/
def pOrbitOK (b : KBox) (e g a : Nat) : Bool :=
  orbNrmOK b e g a &&
    if e = 0 then
      let P := orbGen Int.add Int.sub Int.mul (fun z => z) (fun i => pX i.val) b e g a
      decide (orbErr b e < pLower P.1) && decide (orbErr b e < pLower P.2)
    else
      let P := orbGen Int.add Int.sub Int.mul (fun z => z) qXv b e g a
      decide (orbErr b e < qLower P.1) && decide (orbErr b e < qLower P.2)

/-- Packed kernel domain leaf. -/
def pDomOK (b : KBox) (code : Nat) : Bool :=
  let U := p2 b.K
  if code = 0 then
    let ulo := b.c.getD 0 0 - b.h.getD 0 0
    let vlo := b.c.getD 1 0 - b.h.getD 1 0
    decide (0 ≤ ulo) && decide (0 ≤ vlo) && decide (U * U < ulo * ulo + vlo * vlo)
  else if code = 1 then
    let uhi := b.c.getD 0 0 + b.h.getD 0 0
    let vlo := b.c.getD 1 0 - b.h.getD 1 0
    decide (0 ≤ uhi) && decide (57 * uhi < 128 * vlo)
  else if code < 7 then pChartOK b (code - 2)
  else if code < 67 then
    let i := code - 7
    pOrbitOK b (i / 30) (i / 2 % 15) (if i % 2 = 0 then 0 else 4)
  else false

end Cayley.K

end
