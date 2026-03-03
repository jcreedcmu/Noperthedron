import Noperthedron.SolutionTable.Basic

/-!
# Global Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational global theorem. Everything
here is computable — no `noncomputable` keyword. This file deliberately
reimplements sin/cos Taylor polynomials (which are noncomputable in
`RationalApprox/Basic.lean`) as computable functions over ℚ.
-/

namespace Solution.Checker

/-! ## Constants -/

def DENOMQ : ℚ := 15360000
def κQ : ℚ := 1 / 10 ^ 10

/-! ## Computable sine and cosine (Taylor polynomials in Horner form)

`sinQ x` computes the degree-25 Taylor polynomial of sin:
  x · (1 − x²/(2·3) · (1 − x²/(4·5) · ⋯ (1 − x²/(24·25))))

`cosQ x` computes the degree-24 Taylor polynomial of cos:
  1 − x²/(1·2) · (1 − x²/(3·4) · ⋯ (1 − x²/(23·24)))

These are mathematically identical to `sin_psum 13` and `cos_psum 13`
in `RationalApprox/Basic.lean`, but manifestly computable.
-/

def sinQ (x : ℚ) : ℚ :=
  let x2 := x * x
  x * (1 - x2 / (2*3) * (1 - x2 / (4*5) * (1 - x2 / (6*7) *
      (1 - x2 / (8*9) * (1 - x2 / (10*11) * (1 - x2 / (12*13) *
      (1 - x2 / (14*15) * (1 - x2 / (16*17) * (1 - x2 / (18*19) *
      (1 - x2 / (20*21) * (1 - x2 / (22*23) * (1 - x2 / (24*25)
      ))))))))))))

def cosQ (x : ℚ) : ℚ :=
  let x2 := x * x
  1 - x2 / (1*2) * (1 - x2 / (3*4) * (1 - x2 / (5*6) *
     (1 - x2 / (7*8) * (1 - x2 / (9*10) * (1 - x2 / (11*12) *
     (1 - x2 / (13*14) * (1 - x2 / (15*16) * (1 - x2 / (17*18) *
     (1 - x2 / (19*20) * (1 - x2 / (21*22) * (1 - x2 / (23*24)
     )))))))))))

/-! ## Matrix-vector application

Computable versions of the 2×3 and 2×2 matrix-vector products from
`RationalApprox/Basic.lean`. Each function applies a specific rotation
matrix to a vector and returns the result.
-/

/-- M(θ,φ) · v — the projection matrix. -/
def applyM (θ φ : ℚ) (v : Fin 3 → ℚ) : Fin 2 → ℚ
  | 0 => -(sinQ θ) * v 0 + cosQ θ * v 1
  | 1 => -(cosQ θ) * cosQ φ * v 0 - sinQ θ * cosQ φ * v 1 + sinQ φ * v 2

/-- Mθ(θ,φ) · v — ∂M/∂θ applied to v. -/
def applyMθ (θ φ : ℚ) (v : Fin 3 → ℚ) : Fin 2 → ℚ
  | 0 => -(cosQ θ) * v 0 - sinQ θ * v 1
  | 1 => sinQ θ * cosQ φ * v 0 - cosQ θ * cosQ φ * v 1

/-- Mφ(θ,φ) · v — ∂M/∂φ applied to v. -/
def applyMφ (θ φ : ℚ) (v : Fin 3 → ℚ) : Fin 2 → ℚ
  | 0 => 0
  | 1 => cosQ θ * sinQ φ * v 0 + sinQ θ * sinQ φ * v 1 + cosQ φ * v 2

/-- R(α) · u — in-plane rotation. -/
def applyR (α : ℚ) (u : Fin 2 → ℚ) : Fin 2 → ℚ
  | 0 => cosQ α * u 0 - sinQ α * u 1
  | 1 => sinQ α * u 0 + cosQ α * u 1

/-- R'(α) · u — derivative of in-plane rotation. -/
def applyR' (α : ℚ) (u : Fin 2 → ℚ) : Fin 2 → ℚ
  | 0 => -(sinQ α) * u 0 - cosQ α * u 1
  | 1 => cosQ α * u 0 - sinQ α * u 1

/-! ## Rational vertex data

90 rational approximations of the noperthedron vertices, hard-coded from
Python's `⌊exact·10¹⁶⌋/10¹⁶` computation. Indexing convention:
`index = k + 15·i + 45·ℓ` where k ∈ [0,15), i ∈ {0,1,2}, ℓ ∈ {0,1}.
-/

private def d : ℚ := 10^16

private def mkV (a b c : ℤ) : Fin 3 → ℚ :=
  fun | 0 => ↑a / d | 1 => ↑b / d | 2 => ↑c / d

def nopertListQ : Array (Fin 3 → ℚ) := #[
  mkV     5861195714524832                    0     8102245663767282, -- [0] ℓ=0 i=0 k=0
  mkV     5354468721358439     2383963069336096     8102245663767282, -- [1] ℓ=0 i=0 k=1
  mkV     3921905442447942     4355717266359407     8102245663767282, -- [2] ℓ=0 i=0 k=2
  mkV     1811209083145786     5574328377580070     8102245663767282, -- [3] ℓ=0 i=0 k=3
  mkV     (-612661780950237)     5829087471133637     8102245663767282, -- [4] ℓ=0 i=0 k=4
  mkV    (-2930597857262417)     5075944385330989     8102245663767282, -- [5] ℓ=0 i=0 k=5
  mkV    (-4741806940408203)     3445124401797541     8102245663767282, -- [6] ℓ=0 i=0 k=6
  mkV    (-5733114525593729)     1218611111220663     8102245663767282, -- [7] ℓ=0 i=0 k=7
  mkV    (-5733114525593729)    (-1218611111220664)     8102245663767282, -- [8] ℓ=0 i=0 k=8
  mkV    (-4741806940408203)    (-3445124401797542)     8102245663767282, -- [9] ℓ=0 i=0 k=9
  mkV    (-2930597857262417)    (-5075944385330990)     8102245663767282, -- [10] ℓ=0 i=0 k=10
  mkV     (-612661780950237)    (-5829087471133638)     8102245663767282, -- [11] ℓ=0 i=0 k=11
  mkV     1811209083145786    (-5574328377580071)     8102245663767282, -- [12] ℓ=0 i=0 k=12
  mkV     3921905442447942    (-4355717266359408)     8102245663767282, -- [13] ℓ=0 i=0 k=13
  mkV     5354468721358439    (-2383963069336097)     8102245663767282, -- [14] ℓ=0 i=0 k=14
  mkV     6632738028000000     6106948881000000     3980949609000000, -- [15] ℓ=0 i=1 k=0
  mkV     3575387809919287     8276753010203037     3980949609000000, -- [16] ℓ=0 i=1 k=1
  mkV     (-100179441875016)     9015431352001416     3980949609000000, -- [17] ℓ=0 i=1 k=2
  mkV    (-3758424758067471)     8195259710416135     3980949609000000, -- [18] ℓ=0 i=1 k=3
  mkV    (-6766804289373043)     5958053213302737     3980949609000000, -- [19] ℓ=0 i=1 k=4
  mkV    (-8605141884558951)     2690645188395101     3980949609000000, -- [20] ℓ=0 i=1 k=5
  mkV    (-8955572272644798)    (-1041999833330208)     3980949609000000, -- [21] ℓ=0 i=1 k=6
  mkV    (-7757502855970407)    (-4594473617601419)     3980949609000000, -- [22] ℓ=0 i=1 k=7
  mkV    (-5218090720797741)    (-7352521173906880)     3980949609000000, -- [23] ℓ=0 i=1 k=8
  mkV    (-1776423295133155)    (-8839251023685930)     3980949609000000, -- [24] ℓ=0 i=1 k=9
  mkV     1972403856558950    (-8797594069395102)     3980949609000000, -- [25] ℓ=0 i=1 k=10
  mkV     5380184462725509    (-7234753176872830)     3980949609000000, -- [26] ℓ=0 i=1 k=11
  mkV     7857682297845422    (-4420957734399999)     3980949609000000, -- [27] ℓ=0 i=1 k=12
  mkV     8976515478865210     (-842738536509256)     3980949609000000, -- [28] ℓ=0 i=1 k=13
  mkV     8543227584506196     2881197810383191     3980949609000000, -- [29] ℓ=0 i=1 k=14
  mkV     8193990033000000     5298215096000000     1230614493000000, -- [30] ℓ=0 i=2 k=0
  mkV     5330604152175326     8172956333983242     1230614493000000, -- [31] ℓ=0 i=2 k=1
  mkV     1545508386421115     9634519172843429     1230614493000000, -- [32] ℓ=0 i=2 k=2
  mkV    (-2506819819848217)     9430186119860083     1230614493000000, -- [33] ℓ=0 i=2 k=3
  mkV    (-6125696105522678)     7595288216201537     1230614493000000, -- [34] ℓ=0 i=2 k=4
  mkV    (-8685383884350209)     4447095978934490     1230614493000000, -- [35] ℓ=0 i=2 k=5
  mkV    (-9743289885338086)      529960446311021     1230614493000000, -- [36] ℓ=0 i=2 k=6
  mkV    (-9116492550141204)    (-3478810062019133)     1230614493000000, -- [37] ℓ=0 i=2 k=7
  mkV    (-6913370832290130)    (-6886062706628928)     1230614493000000, -- [38] ℓ=0 i=2 k=8
  mkV    (-3514864491533787)    (-9102652551346809)     1230614493000000, -- [39] ℓ=0 i=2 k=9
  mkV      491393851350208    (-9745311074934491)     1230614493000000, -- [40] ℓ=0 i=2 k=10
  mkV     4412685733162759    (-8702916780294264)     1230614493000000, -- [41] ℓ=0 i=2 k=11
  mkV     7570984163720088    (-6155709110824297)     1230614493000000, -- [42] ℓ=0 i=2 k=12
  mkV     9420190652138346    (-2544123413231157)     1230614493000000, -- [43] ℓ=0 i=2 k=13
  mkV     9640560597056463     1507364335145271     1230614493000000, -- [44] ℓ=0 i=2 k=14
  mkV    (-5861195714524833)                    0    (-8102245663767283), -- [45] ℓ=1 i=0 k=0
  mkV    (-5354468721358440)    (-2383963069336097)    (-8102245663767283), -- [46] ℓ=1 i=0 k=1
  mkV    (-3921905442447943)    (-4355717266359408)    (-8102245663767283), -- [47] ℓ=1 i=0 k=2
  mkV    (-1811209083145787)    (-5574328377580071)    (-8102245663767283), -- [48] ℓ=1 i=0 k=3
  mkV      612661780950236    (-5829087471133638)    (-8102245663767283), -- [49] ℓ=1 i=0 k=4
  mkV     2930597857262416    (-5075944385330990)    (-8102245663767283), -- [50] ℓ=1 i=0 k=5
  mkV     4741806940408202    (-3445124401797542)    (-8102245663767283), -- [51] ℓ=1 i=0 k=6
  mkV     5733114525593728    (-1218611111220664)    (-8102245663767283), -- [52] ℓ=1 i=0 k=7
  mkV     5733114525593728     1218611111220663    (-8102245663767283), -- [53] ℓ=1 i=0 k=8
  mkV     4741806940408202     3445124401797541    (-8102245663767283), -- [54] ℓ=1 i=0 k=9
  mkV     2930597857262416     5075944385330989    (-8102245663767283), -- [55] ℓ=1 i=0 k=10
  mkV      612661780950236     5829087471133637    (-8102245663767283), -- [56] ℓ=1 i=0 k=11
  mkV    (-1811209083145787)     5574328377580070    (-8102245663767283), -- [57] ℓ=1 i=0 k=12
  mkV    (-3921905442447943)     4355717266359407    (-8102245663767283), -- [58] ℓ=1 i=0 k=13
  mkV    (-5354468721358440)     2383963069336096    (-8102245663767283), -- [59] ℓ=1 i=0 k=14
  mkV    (-6632738028000000)    (-6106948881000000)    (-3980949609000000), -- [60] ℓ=1 i=1 k=0
  mkV    (-3575387809919288)    (-8276753010203038)    (-3980949609000000), -- [61] ℓ=1 i=1 k=1
  mkV      100179441875015    (-9015431352001417)    (-3980949609000000), -- [62] ℓ=1 i=1 k=2
  mkV     3758424758067470    (-8195259710416136)    (-3980949609000000), -- [63] ℓ=1 i=1 k=3
  mkV     6766804289373042    (-5958053213302738)    (-3980949609000000), -- [64] ℓ=1 i=1 k=4
  mkV     8605141884558950    (-2690645188395102)    (-3980949609000000), -- [65] ℓ=1 i=1 k=5
  mkV     8955572272644797     1041999833330207    (-3980949609000000), -- [66] ℓ=1 i=1 k=6
  mkV     7757502855970406     4594473617601418    (-3980949609000000), -- [67] ℓ=1 i=1 k=7
  mkV     5218090720797740     7352521173906879    (-3980949609000000), -- [68] ℓ=1 i=1 k=8
  mkV     1776423295133154     8839251023685929    (-3980949609000000), -- [69] ℓ=1 i=1 k=9
  mkV    (-1972403856558951)     8797594069395101    (-3980949609000000), -- [70] ℓ=1 i=1 k=10
  mkV    (-5380184462725510)     7234753176872829    (-3980949609000000), -- [71] ℓ=1 i=1 k=11
  mkV    (-7857682297845423)     4420957734399998    (-3980949609000000), -- [72] ℓ=1 i=1 k=12
  mkV    (-8976515478865211)      842738536509255    (-3980949609000000), -- [73] ℓ=1 i=1 k=13
  mkV    (-8543227584506197)    (-2881197810383192)    (-3980949609000000), -- [74] ℓ=1 i=1 k=14
  mkV    (-8193990033000000)    (-5298215096000000)    (-1230614493000000), -- [75] ℓ=1 i=2 k=0
  mkV    (-5330604152175327)    (-8172956333983243)    (-1230614493000000), -- [76] ℓ=1 i=2 k=1
  mkV    (-1545508386421116)    (-9634519172843430)    (-1230614493000000), -- [77] ℓ=1 i=2 k=2
  mkV     2506819819848216    (-9430186119860084)    (-1230614493000000), -- [78] ℓ=1 i=2 k=3
  mkV     6125696105522677    (-7595288216201538)    (-1230614493000000), -- [79] ℓ=1 i=2 k=4
  mkV     8685383884350208    (-4447095978934491)    (-1230614493000000), -- [80] ℓ=1 i=2 k=5
  mkV     9743289885338085     (-529960446311022)    (-1230614493000000), -- [81] ℓ=1 i=2 k=6
  mkV     9116492550141203     3478810062019132    (-1230614493000000), -- [82] ℓ=1 i=2 k=7
  mkV     6913370832290129     6886062706628927    (-1230614493000000), -- [83] ℓ=1 i=2 k=8
  mkV     3514864491533786     9102652551346808    (-1230614493000000), -- [84] ℓ=1 i=2 k=9
  mkV     (-491393851350209)     9745311074934490    (-1230614493000000), -- [85] ℓ=1 i=2 k=10
  mkV    (-4412685733162760)     8702916780294263    (-1230614493000000), -- [86] ℓ=1 i=2 k=11
  mkV    (-7570984163720089)     6155709110824296    (-1230614493000000), -- [87] ℓ=1 i=2 k=12
  mkV    (-9420190652138347)     2544123413231156    (-1230614493000000), -- [88] ℓ=1 i=2 k=13
  mkV    (-9640560597056464)    (-1507364335145272)    (-1230614493000000)  -- [89] ℓ=1 i=2 k=14
]

/-- Get vertex by index, defaulting to zero for out-of-bounds. -/
def getVertex (idx : ℕ) : Fin 3 → ℚ :=
  nopertListQ.getD idx (fun _ => 0)

/-! ## Helper functions -/

/-- Center of an interval box along one parameter, as a rational. -/
def centerQ (iv : Interval) (p : Param) : ℚ :=
  (iv.min p + iv.max p) / (2 * DENOMQ)

/-- Max half-width of an interval box across all 5 parameters. -/
def epsilonQ (iv : Interval) : ℚ :=
  let hw (p : Param) := (iv.max p - iv.min p) / (2 * DENOMQ)
  max (hw .θ₁) (max (hw .φ₁) (max (hw .θ₂) (max (hw .φ₂) (hw .α))))

/-- 2D dot product. -/
def dot2 (u w : Fin 2 → ℚ) : ℚ := u 0 * w 0 + u 1 * w 1

/-! ## Gℚ and Hℚ computation

Direct rational computation matching the formulas in
`RationalApprox/RationalGlobal.lean`.
-/

/-- Rational G function: measures how far inner-shadow vertex S sticks out. -/
def computeGQ (θ₁ φ₁ α ε : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) : ℚ :=
  let m1S := applyM θ₁ φ₁ S
  let inner := dot2 (applyR α m1S) w
  let t1 := |dot2 (applyR' α m1S) w|
  let t2 := |dot2 (applyR α (applyMθ θ₁ φ₁ S)) w|
  let t3 := |dot2 (applyR α (applyMφ θ₁ φ₁ S)) w|
  inner - ε * (t1 + t2 + t3) - 9 * ε ^ 2 / 2 - 4 * κQ * (1 + 3 * ε)

/-- Rational H function: measures how far outer-shadow vertex P reaches. -/
def computeHQ (θ₂ φ₂ ε : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) : ℚ :=
  let m2P := applyM θ₂ φ₂ P
  let outer := dot2 m2P w
  let t1 := |dot2 (applyMθ θ₂ φ₂ P) w|
  let t2 := |dot2 (applyMφ θ₂ φ₂ P) w|
  outer + ε * (t1 + t2) + 2 * ε ^ 2 + 3 * κQ * (1 + 2 * ε)

/-- Maximum H over all 90 vertices. -/
def computeMaxHQ (θ₂ φ₂ ε : ℚ) (w : Fin 2 → ℚ) : ℚ :=
  let values := nopertListQ.map (computeHQ θ₂ φ₂ ε w)
  values.foldl max (values.getD 0 0)

/-! ## The main checker -/

/-- Check whether a row constitutes a valid application of the rational
global theorem. Returns `true` iff all preconditions are satisfied. -/
def checkGlobal (row : Row) : Bool :=
  let iv := row.interval
  let θ₁ := centerQ iv .θ₁
  let φ₁ := centerQ iv .φ₁
  let θ₂ := centerQ iv .θ₂
  let φ₂ := centerQ iv .φ₂
  let α := centerQ iv .α
  let ε := epsilonQ iv
  let S := getVertex row.S_index.val
  let w : Fin 2 → ℚ := fun
    | 0 => row.wx_numerator / row.w_denominator
    | 1 => row.wy_numerator / row.w_denominator
  -- (1) Node type must be global
  row.nodeType == 1
  -- (2) Unit vector: wx² + wy² = w_denom²
  && row.wx_numerator ^ 2 + row.wy_numerator ^ 2 == (row.w_denominator : ℤ) ^ 2
  -- (3) w_denominator is positive
  && decide (row.w_denominator > 0)
  -- (4) Center pose in [-4, 4]⁵
  && decide (-4 ≤ θ₁) && decide (θ₁ ≤ 4)
  && decide (-4 ≤ φ₁) && decide (φ₁ ≤ 4)
  && decide (-4 ≤ θ₂) && decide (θ₂ ≤ 4)
  && decide (-4 ≤ φ₂) && decide (φ₂ ≤ 4)
  && decide (-4 ≤ α) && decide (α ≤ 4)
  -- (5) Positive epsilon
  && decide (ε > 0)
  -- (6) G > maxH inequality
  && decide (computeGQ θ₁ φ₁ α ε S w > computeMaxHQ θ₂ φ₂ ε w)

/-! ## Smoke tests

Auto-generated from `data/solution_tree_300.csv`.
To regenerate: `python3 scripts/gen_global_tests.py 30`
-/

-- Auto-generated from data/solution_tree_300.csv (30 global rows)
-- To regenerate: python3 scripts/gen_global_tests.py 30

private def testRow91 : Row := {
  ID := 91, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 5319166373, wy_numerator := 15662395164,
  w_denominator := 16540984045,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow92 : Row := {
  ID := 92, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 806400 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 806400 | .φ₁ => 1612800 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 9859861492, wy_numerator := 3591020715,
  w_denominator := 10493440733,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow94 : Row := {
  ID := 94, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 806400 | .θ₂ => 0
                            | .φ₂ => 808960 | .α => -24268800,
                max := fun | .θ₁ => 806400 | .φ₁ => 1612800 | .θ₂ => 806400
                            | .φ₂ => 1617920 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 2341529500, wy_numerator := 919459749,
  w_denominator := 2515584749,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow95 : Row := {
  ID := 95, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 806400 | .θ₂ => 0
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 806400 | .φ₁ => 1612800 | .θ₂ => 806400
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 19348165624, wy_numerator := 61980254193,
  w_denominator := 64929988625,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow98 : Row := {
  ID := 98, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -24268800,
                max := fun | .θ₁ => 806400 | .φ₁ => 1612800 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -23459840 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 7125455960, wy_numerator := 19125400809,
  w_denominator := 20409632009,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow99 : Row := {
  ID := 99, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 806400 | .φ₁ => 1612800 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 5319166373, wy_numerator := 15662395164,
  w_denominator := 16540984045,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow107 : Row := {
  ID := 107, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 0 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 1612800 | .φ₁ => 806400 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := ⟨85, by omega⟩,
  wx_numerator := 36380760, wy_numerator := -543260641,
  w_denominator := 544477441,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow108 : Row := {
  ID := 108, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 1612800 | .φ₁ => 1612800 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840 },
  S_index := ⟨35, by omega⟩,
  wx_numerator := 630691044, wy_numerator := -357161717,
  w_denominator := 724800445,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow109 : Row := {
  ID := 109, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -23459840,
                max := fun | .θ₁ => 1612800 | .φ₁ => 1612800 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -22650880 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 9859861492, wy_numerator := 3591020715,
  w_denominator := 10493440733,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow110 : Row := {
  ID := 110, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 0
                            | .φ₂ => 808960 | .α => -24268800,
                max := fun | .θ₁ => 1612800 | .φ₁ => 1612800 | .θ₂ => 806400
                            | .φ₂ => 1617920 | .α => -23459840 },
  S_index := ⟨35, by omega⟩,
  wx_numerator := 804988240, wy_numerator := -494376951,
  w_denominator := 944677001,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow111 : Row := {
  ID := 111, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 0
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 1612800 | .φ₁ => 1612800 | .θ₂ => 806400
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 2341529500, wy_numerator := 919459749,
  w_denominator := 2515584749,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow112 : Row := {
  ID := 112, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 1612800 | .φ₁ => 1612800 | .θ₂ => 1612800
                            | .φ₂ => 808960 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 316700391, wy_numerator := 96278600,
  w_denominator := 331011641,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow114 : Row := {
  ID := 114, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -24268800,
                max := fun | .θ₁ => 1612800 | .φ₁ => 1612800 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 59674116501, wy_numerator := 19533781940,
  w_denominator := 62789878301,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow115 : Row := {
  ID := 115, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 1612800 | .φ₁ => 1612800 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 7125455960, wy_numerator := 19125400809,
  w_denominator := 20409632009,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow116 : Row := {
  ID := 116, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -23864320 },
  S_index := ⟨36, by omega⟩,
  wx_numerator := 418569037, wy_numerator := -28741284,
  w_denominator := 419554645,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow117 : Row := {
  ID := 117, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -23864320,
                max := fun | .θ₁ => 403200 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 200916921, wy_numerator := 74937200,
  w_denominator := 214436921,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow118 : Row := {
  ID := 118, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 0
                            | .φ₂ => 404480 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 808960 | .α => -23864320 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 2482999140, wy_numerator := 959805749,
  w_denominator := 2662050301,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow119 : Row := {
  ID := 119, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 0
                            | .φ₂ => 404480 | .α => -23864320,
                max := fun | .θ₁ => 403200 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 808960 | .α => -23459840 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 47131693972, wy_numerator := 134799139965,
  w_denominator := 142801276997,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow120 : Row := {
  ID := 120, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 403200
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 403200 | .θ₂ => 806400
                            | .φ₂ => 404480 | .α => -23864320 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 1141600345, wy_numerator := 391466208,
  w_denominator := 1206854233,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow122 : Row := {
  ID := 122, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 403200 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23864320 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 17912906816, wy_numerator := 47156086713,
  w_denominator := 50443718585,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow123 : Row := {
  ID := 123, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -23864320,
                max := fun | .θ₁ => 403200 | .φ₁ => 403200 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840 },
  S_index := ⟨39, by omega⟩,
  wx_numerator := 17912906816, wy_numerator := 47156086713,
  w_denominator := 50443718585,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow124 : Row := {
  ID := 124, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -23864320 },
  S_index := ⟨36, by omega⟩,
  wx_numerator := 418569037, wy_numerator := -28741284,
  w_denominator := 419554645,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow125 : Row := {
  ID := 125, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -23864320,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 200916921, wy_numerator := 74937200,
  w_denominator := 214436921,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow126 : Row := {
  ID := 126, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 0
                            | .φ₂ => 404480 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 403200
                            | .φ₂ => 808960 | .α => -23864320 },
  S_index := ⟨36, by omega⟩,
  wx_numerator := 5456912188, wy_numerator := -387511245,
  w_denominator := 5470654037,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow127 : Row := {
  ID := 127, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 0
                            | .φ₂ => 404480 | .α => -23864320,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 403200
                            | .φ₂ => 808960 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 2482999140, wy_numerator := 959805749,
  w_denominator := 2662050301,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow128 : Row := {
  ID := 128, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 404480 | .α => -23864320 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 1141600345, wy_numerator := 391466208,
  w_denominator := 1206854233,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow129 : Row := {
  ID := 129, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 0 | .α => -23864320,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 404480 | .α => -23459840 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 1141600345, wy_numerator := 391466208,
  w_denominator := 1206854233,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow130 : Row := {
  ID := 130, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -24268800,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23864320 },
  S_index := ⟨37, by omega⟩,
  wx_numerator := 846860385, wy_numerator := 300865912,
  w_denominator := 898717313,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow131 : Row := {
  ID := 131, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -23864320,
                max := fun | .θ₁ => 403200 | .φ₁ => 806400 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840 },
  S_index := ⟨38, by omega⟩,
  wx_numerator := 3235387544, wy_numerator := 3187166367,
  w_denominator := 4541559425,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def testRow132 : Row := {
  ID := 132, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 403200 | .φ₁ => 0 | .θ₂ => 0
                            | .φ₂ => 0 | .α => -24268800,
                max := fun | .θ₁ => 806400 | .φ₁ => 403200 | .θ₂ => 403200
                            | .φ₂ => 404480 | .α => -23864320 },
  S_index := ⟨36, by omega⟩,
  wx_numerator := 418569037, wy_numerator := -28741284,
  w_denominator := 419554645,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

private def globalTestRows : Array Row := #[
  testRow91, testRow92, testRow94, testRow95, testRow98, testRow99,
  testRow107, testRow108, testRow109, testRow110, testRow111, testRow112,
  testRow114, testRow115, testRow116, testRow117, testRow118, testRow119,
  testRow120, testRow122, testRow123, testRow124, testRow125, testRow126,
  testRow127, testRow128, testRow129, testRow130, testRow131, testRow132
]

/-- info: All 30 global rows pass -/
#guard_msgs in
#eval show IO Unit from do
  let failures ← globalTestRows.toList.foldlM (init := (#[] : Array Nat)) fun acc row => do
    if checkGlobal row then pure acc else pure (acc.push row.ID)
  if failures.isEmpty then IO.println "All 30 global rows pass"
  else IO.println s!"FAILED rows: {failures}"

end Solution.Checker
