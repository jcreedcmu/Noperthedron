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
  /-- The tie cone's strong-coordinate scale multiplier (capcert `--mcone_strong_mul`). -/
  mcm : ℕ
  x : KVec
  e1 : KVec
  e2 : KVec
  /-- Base charts using the tie scheme (capcert `--tie_charts`) and their (Z₂, K, K'). -/
  tieCharts : List ((Kind × ℕ × ℕ × Bool) × (ℕ × ℕ × ℕ)) := []

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
deriving DecidableEq, Repr

def Setup.strong (st : Setup) (i : ℕ) : Bool := if st.aniso then 1 ≤ i else i = 2
def Setup.range (st : Setup) (i : ℕ) : ℕ := if st.strong i then st.strongScale else 2
/-- The cone charts' coordinate scale ⌊Rᵢ/2⌋ (times `mcm` for the tie cone's strong coordinates). -/
def Setup.coneScale (st : Setup) (k : Kind) (i : ℕ) : ℤ :=
  ((st.range i : ℤ) / 2) * (if k = .mcone ∧ st.strong i = true then (st.mcm : ℤ) else 1)

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

def Setup.tieOf (st : Setup) (b : Kind × ℕ × ℕ × Bool) : Option (ℕ × ℕ × ℕ) :=
  (st.tieCharts.find? (fun e => decide (e.1 = b))).map (·.2)

/-- (e, s₀) of chart m of the tie scheme (capcert ratio 10–17; p₀ = pv 0, s₀'s variable q = pv 1):
10: (μ p₀, μ q); 11/12: (μ p₀, ±(K' μ + q)); 13: (K μ + p₀, μ q); 14: (K μ + p₀, −(Z μ + q));
15: (e, e + μ q); 16: (e, e + Z₂ μ + q); 17: (e, Z μ + q (p₀ + (K − Z − Z₂) μ)), e = K μ + p₀. -/
def tieES (m Z Z2 K Kp : ℕ) : NPoly 5 × NPoly 5 :=
  let p0 := pv 0
  let q := pv 1
  let am (a : ℕ) : NPoly 5 := NPoly.mul 5 (pint a) mu
  let neg (x : NPoly 5) : NPoly 5 := NPoly.scale 5 (-1) x
  let eK := NPoly.add 5 (am K) p0
  if m = 10 then (NPoly.mul 5 mu p0, NPoly.mul 5 mu q)
  else if m = 11 then (NPoly.mul 5 mu p0, NPoly.add 5 (am Kp) q)
  else if m = 12 then (NPoly.mul 5 mu p0, neg (NPoly.add 5 (am Kp) q))
  else if m = 13 then (eK, NPoly.mul 5 mu q)
  else if m = 14 then (eK, neg (NPoly.add 5 (am Z) q))
  else if m = 15 then (eK, NPoly.add 5 eK (NPoly.mul 5 mu q))
  else if m = 16 then (eK, NPoly.add 5 (NPoly.add 5 eK (am Z2)) q)
  else (eK, NPoly.add 5 (am Z) (NPoly.mul 5 q (NPoly.add 5 p0 (am (K - Z - Z2)))))

/-- The tie scheme's (e, s₀) of a chart, if it is one. -/
def Setup.tieChartES (st : Setup) (id : ChartId) : Option (NPoly 5 × NPoly 5) :=
  if 10 ≤ id.ratio ∧ id.kind = .face then
    (st.tieOf (id.kind, id.side, id.axis, id.sign)).map fun p => tieES id.ratio id.z p.1 p.2.1 p.2.2
  else none

/-- A face chart's s (before the tie scheme's s₀). -/
def faceS (st : Setup) (id : ChartId) : Fin 3 → NPoly 5 := fun i =>
  if (i : ℕ) = id.axis then pint ((if id.sign then 1 else -1) * st.range i) else
    match pvarOf id i with
    | some k => ratioVar st id k
    | none => NPoly.zero 5

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
      NPoly.add 5 (center i) (NPoly.mul 5 (NPoly.mul 5 (pint (st.coneScale id.kind i)) (pv 0)) sig))
  | .face =>
    match st.tieChartES id with
    | some es => (es.1, fun i => if (i : ℕ) = 0 then es.2 else faceS st id i)
    | none => (pv 0, faceS st id)

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
  /-- The tie cone's radius (capcert `--t0_mcone`). -/
  t0m : ℚ
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
    if kind = .face ∧ (st.tieOf b).isSome then (List.range 8).map fun m => { base with ratio := 10 + m } else
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
  | .mcone, 2 => (0, pr.t0m)
  | _, 2 => (0, pr.t0)
  | _, _ => (-1, 1)

/-- The tie scheme's bounds of (p₀, p₁) (v = 2, 3) for chart m. -/
def tieLoHi (m Z Z2 K Kp : ℕ) (v : ℕ) : Option (ℚ × ℚ) :=
  if v = 2 then some (if m ≤ 12 then (0, (K : ℚ)) else (0, 1))
  else if v = 3 then some
    (if m = 10 then (-(Kp : ℚ), (Kp : ℚ)) else if m = 13 then (-(Z : ℚ), (Z : ℚ))
     else if m = 15 then (-(Z2 : ℚ), (Z2 : ℚ)) else if m = 17 then (0, 1) else (0, 2))
  else none

def Setup.tieLoHiOf (st : Setup) (id : ChartId) (v : ℕ) : Option (ℚ × ℚ) :=
  if 10 ≤ id.ratio ∧ id.kind = .face then
    match st.tieOf (id.kind, id.side, id.axis, id.sign) with
    | some p => tieLoHi id.ratio id.z p.1 p.2.1 p.2.2 v
    | none => none
  else none

/-- The coordinate bounds of a chart outside the tie scheme. -/
def rootLoHiStd (st : Setup) (pr : Params) (id : ChartId) (v : ℕ) : ℚ × ℚ :=
  if 2 ≤ v then
    if id.ratio = 1 ∧ (List.range 3).any (fun i => !st.strong i && pvarOf id i = some (v - 2)) then
      (-(id.z : ℚ), (id.z : ℚ))
    else if id.ratio = 2 ∧ pvarOf id id.ratioCoord = some (v - 2) then (0, (baseLoHi st pr id.kind id.axis v).2)
    else baseLoHi st pr id.kind id.axis v
  else baseLoHi st pr id.kind id.axis v

/-- A chart's coordinate bounds (lo, hi), as capcert's ChartId box. -/
def rootLoHi (st : Setup) (pr : Params) (id : ChartId) (v : ℕ) : ℚ × ℚ :=
  match st.tieLoHiOf id v with
  | some r => r
  | none => rootLoHiStd st pr id v

theorem rootLoHi_std' (st : Setup) (pr : Params) (id : ChartId) (v : ℕ) (h : st.tieLoHiOf id v = none) :
    rootLoHi st pr id v = rootLoHiStd st pr id v := by
  simp [rootLoHi, h]

theorem rootLoHi_std (st : Setup) (pr : Params) (id : ChartId) (h : id.ratio < 10) (v : ℕ) :
    rootLoHi st pr id v = rootLoHiStd st pr id v := by
  apply rootLoHi_std'
  simp [Setup.tieLoHiOf]; omega

theorem tieLoHiOf_of_ne_face (st : Setup) (id : ChartId) (h : id.kind ≠ .face) (v : ℕ) : st.tieLoHiOf id v = none := by
  simp [Setup.tieLoHiOf, h]

theorem tieLoHiOf_of_v (st : Setup) (id : ChartId) (v : ℕ) (h : v ≠ 2 ∧ v ≠ 3) : st.tieLoHiOf id v = none := by
  unfold Setup.tieLoHiOf
  split_ifs
  · split
    · simp [tieLoHi, h.1, h.2]
    · rfl
  · rfl

/-- The root box of a chart (lo, width). -/
def rootBox (st : Setup) (pr : Params) (id : ChartId) : Fin 5 → ℚ × ℚ :=
  fun v => ((rootLoHi st pr id v).1, (rootLoHi st pr id v).2 - (rootLoHi st pr id v).1)

end Noperthedron.PentagonalHexecontahedron.Cap
