module

public import Noperthedron.PentagonalHexecontahedron.CapPoly

@[expose] public section

/-!
# The charts of the DH cap certificates

A Lean transcription of `MakeChart` in nopert229 `capcert.cc`. The chart
variables are (μ, τ, p₀, p₁, p₂). With (A, B) the frame pair of the chart's
side and a = A + τ B, the view is u = x + μ e a and the Cayley vector is

  u0 (isotropic):  w = μ s₀ e₁ + μ s₁ e₂ + μ² s₂ x
  ux (anisotropic): w = μ s₀ (x × a) + μ² (s₁ a + s₂ x),

where (e, s) depend on the chart kind: F_e (e = 1, s = p), the cones at the
identity and (ux) at the tie (e = 1, s = center + t σ with t = p₀ and σ on a
cube face), and the weighted-cube faces (e = p₀, s on the face). Weak
coordinates may be ratio-blown-up (inner: v ↦ μ v; outer: ±(Z μ + v)).

Only the polynomials are defined here; which poses the charts cover is proved
separately. The witness polynomials are divided by the largest powers of μ
and (cones) t that divide them, and boxes are bounded at the uniform degrees.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

inductive Kind where
  | fe
  | cone
  | mcone
  | face
deriving DecidableEq, Repr

structure Setup where
  aniso : Bool
  halfTurn : Bool
  strongScale : ℕ
  x : KVec
  e1 : KVec
  e2 : KVec

structure ChartId where
  kind : Kind
  side : ℕ
  axis : ℕ
  sign : Bool
  ratio : ℕ
  ratioCoord : ℕ
  ratioSign : Bool
  /-- The ratio blow-up's Z (capcert `--ratio_z`/`--z_override`, exported per chart). -/
  z : ℕ

def Setup.strong (st : Setup) (i : ℕ) : Bool := if st.aniso then 1 ≤ i else i = 2
def Setup.range (st : Setup) (i : ℕ) : ℕ := if st.strong i then st.strongScale else 2

def kint (n : ℤ) : IcoQ := IcoQ.ofRat n
def pint (n : ℤ) : NPoly 5 := NPoly.const 5 (kint n)
def kneg (v : KVec) : KVec := fun i => IcoQ.neg (v i)
def kdot (a b : KVec) : IcoQ := IcoQ.add (IcoQ.mul (a 0) (b 0)) (IcoQ.add (IcoQ.mul (a 1) (b 1)) (IcoQ.mul (a 2) (b 2)))
def kcross (a b : KVec) : KVec :=
  ![IcoQ.sub (IcoQ.mul (a 1) (b 2)) (IcoQ.mul (a 2) (b 1)),
    IcoQ.sub (IcoQ.mul (a 2) (b 0)) (IcoQ.mul (a 0) (b 2)),
    IcoQ.sub (IcoQ.mul (a 0) (b 1)) (IcoQ.mul (a 1) (b 0))]

def mu : NPoly 5 := NPoly.var 5 0
def tau : NPoly 5 := NPoly.var 5 1
def pv (i : ℕ) : NPoly 5 := NPoly.var 5 ⟨(2 + i) % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The chart's (A, B). -/
def Setup.frameAB (st : Setup) (side : ℕ) : KVec × KVec :=
  match side with
  | 0 => (st.e1, st.e2)
  | 1 => (kneg st.e1, st.e2)
  | 2 => (st.e2, st.e1)
  | _ => (kneg st.e2, st.e1)

/-- Which p variable carries coordinate i (none: fixed by the face or cone axis). -/
def pvarOf (id : ChartId) (i : ℕ) : Option ℕ :=
  if id.kind = .fe then some i
  else if i = id.axis then none
  else some (1 + (List.range i).countP (· ≠ id.axis))

/-- The p variables after the ratio substitution. -/
def ratioVar (st : Setup) (id : ChartId) (k : ℕ) : NPoly 5 :=
  if id.ratio = 1 then
    if (List.range 3).any (fun i => !st.strong i && pvarOf id i = some k) then NPoly.mul 5 mu (pv k) else pv k
  else if id.ratio = 2 ∧ pvarOf id id.ratioCoord = some k then
    let inner := NPoly.add 5 (NPoly.mul 5 (pint id.z) mu) (pv k)
    if id.ratioSign then inner else NPoly.scale 5 (-1) inner
  else pv k

/-- (e, s₀, s₁, s₂). -/
def eAndS (st : Setup) (id : ChartId) (A B : KVec) : NPoly 5 × (Fin 3 → NPoly 5) :=
  let sgn : ℤ := if id.sign then 1 else -1
  match id.kind with
  | .fe => (pint 1, fun i => ratioVar st id i)
  | .cone | .mcone =>
    let center : Fin 3 → NPoly 5 := fun i =>
      if id.kind = .mcone then
        if st.aniso then (if (i : ℕ) = 0 then pint 1 else NPoly.zero 5)
        else
          let ex := kcross st.x A
          let fx := kcross st.x B
          if (i : ℕ) = 0 then NPoly.add 5 (NPoly.const 5 (kdot ex st.e1)) (NPoly.mul 5 (NPoly.const 5 (kdot fx st.e1)) tau)
          else if (i : ℕ) = 1 then NPoly.add 5 (NPoly.const 5 (kdot ex st.e2)) (NPoly.mul 5 (NPoly.const 5 (kdot fx st.e2)) tau)
          else NPoly.zero 5
      else NPoly.zero 5
    (pint 1, fun i =>
      let sig := if (i : ℕ) = id.axis then pint sgn else
        match pvarOf id i with
        | some k => ratioVar st id k
        | none => NPoly.zero 5
      NPoly.add 5 (center i) (NPoly.mul 5 (NPoly.mul 5 (pint (st.range i / 2)) (pv 0)) sig))
  | .face =>
    (pv 0, fun i =>
      if (i : ℕ) = id.axis then pint (sgn * st.range i) else
        match pvarOf id i with
        | some k => ratioVar st id k
        | none => NPoly.zero 5)

structure Chart where
  u : PVec
  w : PVec

def makeChart (st : Setup) (id : ChartId) : Chart :=
  let (A, B) := st.frameAB id.side
  let a := PVec.add (PVec.const A) (PVec.smul tau (PVec.const B))
  let (e, s) := eAndS st id A B
  let u := PVec.add (PVec.const st.x) (PVec.smul (NPoly.mul 5 mu e) a)
  let mu2 := NPoly.mul 5 mu mu
  let w :=
    if st.aniso then
      PVec.add (PVec.smul (NPoly.mul 5 mu (s 0)) (PVec.cross (PVec.const st.x) a))
        (PVec.add (PVec.smul (NPoly.mul 5 mu2 (s 1)) a) (PVec.smul (NPoly.mul 5 mu2 (s 2)) (PVec.const st.x)))
    else
      PVec.add (PVec.smul (NPoly.mul 5 mu (s 0)) (PVec.const st.e1))
        (PVec.add (PVec.smul (NPoly.mul 5 mu (s 1)) (PVec.const st.e2)) (PVec.smul (NPoly.mul 5 mu2 (s 2)) (PVec.const st.x)))
  { u := u, w := w }

def isCone (id : ChartId) : Bool := id.kind = .cone || id.kind = .mcone

/-- The divided witness polynomials Q_j (P_j = μ^m t^n Q_j). -/
def witnessPolys (ch : Chart) (id : ChartId) (V : Array KVec) (vk c : KVec) : Array (NPoly 5) :=
  let parts := witnessParts ch.u ch.w vk c
  V.map fun vj =>
    let q := NPoly.divOut 5 0 64 (witnessPoly parts vj)
    if isCone id then NPoly.divOut 5 2 64 q else q

def degs (p : NPoly 5) : Fin 5 → ℕ := fun i => NPoly.degIn 5 i p

/-- A box (lo, width per variable) passes witness Q if every Q_j is ≥ 0 on it. -/
def boxOk (Q : Array (NPoly 5)) (box : Fin 5 → ℚ × ℚ) : Bool :=
  Q.all fun q => decide (0 ≤ NPoly.lowerDeg 5 (degs q) q box)

/-! ### The chart list (capcert's enumeration) -/

/-- The cap's numeric parameters (exported by capcert). -/
structure Params where
  mu0 : ℚ
  t0 : ℚ
  tieCones : Bool
  ratioOn : Bool

/-- The base charts: per side, F_e, then per axis and sign the identity cone, the tie cone (if
any) and the face. -/
def baseCharts (pr : Params) : List (Kind × ℕ × ℕ × Bool) :=
  (List.range 4).flatMap fun side =>
    (Kind.fe, side, 0, true) ::
      ((List.range 3).flatMap fun ax => [true, false].flatMap fun sg =>
        [(Kind.cone, side, ax, sg)] ++ (if pr.tieCones then [(Kind.mcone, side, ax, sg)] else []) ++
          [(Kind.face, side, ax, sg)])

/-- A base chart's ratio blow-ups (when dominated by a strong coordinate). -/
def expandChart (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ)
    (b : Kind × ℕ × ℕ × Bool) : List ChartId :=
  let (kind, side, axis, sign) := b
  let base : ChartId := ⟨kind, side, axis, sign, 0, 0, true, zOf b⟩
  if pr.ratioOn && (kind = .fe || st.strong axis) then
    { base with ratio := 1 } ::
      ((List.range 3).flatMap fun i =>
        if !st.strong i && (pvarOf base i).isSome then
          [{ base with ratio := 2, ratioCoord := i, ratioSign := true },
           { base with ratio := 2, ratioCoord := i, ratioSign := false }]
        else [])
  else [base]

def chartList (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ) : List ChartId :=
  (baseCharts pr).flatMap (expandChart st pr zOf)

/-- The base chart's coordinate bounds (lo, hi), before the ratio substitution. -/
def baseLoHi (st : Setup) (pr : Params) (kind : Kind) (axis : ℕ) (v : ℕ) : ℚ × ℚ :=
  let r : ℕ → ℚ := fun i => (st.range i : ℚ)
  match kind, v with
  | _, 0 => (0, pr.mu0)
  | _, 1 => (-1, 1)
  | .fe, k => (-r (k - 2), r (k - 2))
  | .face, 2 => (0, 1)
  | .face, k => let free := (List.range 3).filter (· ≠ axis); (-r (free.getD (k - 3) 0), r (free.getD (k - 3) 0))
  | _, 2 => (0, pr.t0)
  | _, _ => (-1, 1)

/-- A chart's coordinate bounds (lo, hi), as capcert's ChartId box. -/
def rootLoHi (st : Setup) (pr : Params) (id : ChartId) (v : ℕ) : ℚ × ℚ :=
  if 2 ≤ v then
    if id.ratio = 1 ∧ (List.range 3).any (fun i => !st.strong i && pvarOf id i = some (v - 2)) then
      (-(id.z : ℚ), (id.z : ℚ))
    else if id.ratio = 2 ∧ pvarOf id id.ratioCoord = some (v - 2) then (0, (baseLoHi st pr id.kind id.axis v).2)
    else baseLoHi st pr id.kind id.axis v
  else baseLoHi st pr id.kind id.axis v

/-- The root box of a chart (lo, width). -/
def rootBox (st : Setup) (pr : Params) (id : ChartId) : Fin 5 → ℚ × ℚ :=
  fun v => ((rootLoHi st pr id v).1, (rootLoHi st pr id v).2 - (rootLoHi st pr id v).1)

end Noperthedron.PentagonalHexecontahedron.Cap
