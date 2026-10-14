module

public import Cayley.Checker.KGen
public import Cayley.Checker.KTab
public import Cayley.Checker.Check

@[expose] public section

/-!
# The kernel gap-leaf checker

The same test as `gapOK`, reorganized for `decide +kernel`: integer coefficients at explicit
power-of-two scales, fixed-size polynomial structures (`Cayley.Checker.KGen`), and the
blown-up Cayley numerator built from `N(ρc)S = (1 − ρ²|c|²)S + 2ρ² c (c·S) + 2ρ c×S`.

Scales: box coordinates are integers over `U = 2^K`; vertices are integers over `2^160`.
-/

namespace Cayley.K

/-- A box with integer coordinates over `2^K`. -/
structure KBox where
  chart : Nat
  face : Nat
  K : Nat
  c : List Int
  h : List Int
deriving Inhabited

/-- The vertices, exactly `vertexTab`, as integers over `2^160`. -/
def vtxI : List (Int × Int × Int) := [
  (856614713349491466445980334776951882203105591296, 0, 1184144530365309185986056276372037852756722057216),
  (969375748790894420514575470810276029809469423616, 892531578867762540304363363123470820508784656384, 581816437168531777583991323662460237375659311104),
  (1197552984950259923465160554960708301953477640192, 774335003773530698853721249916154869844361084928, 179854509644263896791744904561535746804316897280),
  (-856614713349491466445980334776951882203105591296, 0, -1184144530365309185986056276372037852756722057216),
  (-969375748790894420514575470810276029809469423616, -892531578867762540304363363123470820508784656384, -581816437168531777583991323662460237375659311104),
  (-1197552984950259923465160554960708301953477640192, -774335003773530698853721249916154869844361084928, -179854509644263896791744904561535746804316897280),
  (782556480330246564330675053333778761834204556661, 348416592917111018056397635365754245654125578187, 1184144530365309185986056276372037852756722057216),
  (522543513828999009409094200456471698805856558133, 1209648807619521853011736933626000434190334848571, 581816437168531777583991323662460237375659311104),
  (779068669636714981724624864750823612270423893606, 1194478906395048201934658416497524489564396650322, 179854509644263896791744904561535746804316897280),
  (-782556480330246564330675053333778761834204556661, -348416592917111018056397635365754245654125578187, -1184144530365309185986056276372037852756722057216),
  (-522543513828999009409094200456471698805856558133, -1209648807619521853011736933626000434190334848571, -581816437168531777583991323662460237375659311104),
  (-779068669636714981724624864750823612270423893606, -1194478906395048201934658416497524489564396650322, -179854509644263896791744904561535746804316897280),
  (573187122559464740704731304533219879877681262703, 636588791653475925452805816347141811539579360947, 1184144530365309185986056276372037852756722057216),
  (-14641241832723120857533190066602624457893100225, 1317606768219442620396595810629459769588334542099, 581816437168531777583991323662460237375659311104),
  (225876303726310149983985464973475812147802705210, 1408086554600664795308850364968755800868415446298, 179854509644263896791744904561535746804316897280),
  (-573187122559464740704731304533219879877681262703, -636588791653475925452805816347141811539579360947, -1184144530365309185986056276372037852756722057216),
  (14641241832723120857533190066602624457893100225, -1317606768219442620396595810629459769588334542099, -581816437168531777583991323662460237375659311104),
  (-225876303726310149983985464973475812147802705210, -1408086554600664795308850364968755800868415446298, -179854509644263896791744904561535746804316897280),
  (264708504056617004608304723490796058086544247602, 814689005085338937022447060041603338324228316873, 1184144530365309185986056276372037852756722057216),
  (-549294393770061081631559494047217153044613924150, 1197738548512516295214190109176694725732475379841, 581816437168531777583991323662460237375659311104),
  (-366372127120172733848433289543119915189762624360, 1378223245451066705795596858301672705159167971082, 179854509644263896791744904561535746804316897280),
  (-264708504056617004608304723490796058086544247602, -814689005085338937022447060041603338324228316873, -1184144530365309185986056276372037852756722057216),
  (549294393770061081631559494047217153044613924150, -1197738548512516295214190109176694725732475379841, -581816437168531777583991323662460237375659311104),
  (366372127120172733848433289543119915189762624360, -1378223245451066705795596858301672705159167971082, -179854509644263896791744904561535746804316897280),
  (-89540619598883826499379453879423452277543225540, 851922088320686409438477687277413043920734976792, 1184144530365309185986056276372037852756722057216),
  (-988969554841647825278379502373278246212289551908, 870770452654659845569316313933819697689332865272, 581816437168531777583991323662460237375659311104),
  (-895271488801292852057881574053534418294016010536, 1110052616397865997915604547462264155197496520064, 179854509644263896791744904561535746804316897280),
  (89540619598883826499379453879423452277543225540, -851922088320686409438477687277413043920734976792, -1184144530365309185986056276372037852756722057216),
  (988969554841647825278379502373278246212289551908, -870770452654659845569316313933819697689332865272, -581816437168531777583991323662460237375659311104),
  (895271488801292852057881574053534418294016010536, -1110052616397865997915604547462264155197496520064, -179854509644263896791744904561535746804316897280),
  (-428307356674745733222990167388475941101552795648, 741850103016184513611710749990487004819930149958, 1184144530365309185986056276372037852756722057216),
  (-1257642895374763811853594601666635484779859964240, 393238234831595633691505013632587627159350603126, 581816437168531777583991323662460237375659311104),
  (-1269370276782526708442136700498935906110514053640, 649943805458043278689043347719582282971169122252, 179854509644263896791744904561535746804316897280),
  (428307356674745733222990167388475941101552795648, -741850103016184513611710749990487004819930149958, -1184144530365309185986056276372037852756722057216),
  (1257642895374763811853594601666635484779859964240, -393238234831595633691505013632587627159350603126, -581816437168531777583991323662460237375659311104),
  (1269370276782526708442136700498935906110514053640, -649943805458043278689043347719582282971169122252, -179854509644263896791744904561535746804316897280),
  (-693015860731362737831294890879271999188097043250, 503505495403575391382080051911658798266609398605, 1184144530365309185986056276372037852756722057216),
  (-1308858353970560661834751888839740221975168246170, -152288446251062659432575961537441632378976132795, 581816437168531777583991323662460237375659311104),
  (-1423983412041123804067543412936566894244109100640, 77453806000417427622715458583492097582807194210, 179854509644263896791744904561535746804316897280),
  (693015860731362737831294890879271999188097043250, -503505495403575391382080051911658798266609398605, -1184144530365309185986056276372037852756722057216),
  (1308858353970560661834751888839740221975168246170, 152288446251062659432575961537441632378976132795, -581816437168531777583991323662460237375659311104),
  (1423983412041123804067543412936566894244109100640, -77453806000417427622715458583492097582807194210, -179854509644263896791744904561535746804316897280),
  (-837895626616081745313036028024015937964225510305, 178100213431863011569641243694461526784648955926, 1184144530365309185986056276372037852756722057216),
  (-1133760312559990497564353262778597878054340066809, -671483071479810965456562582319435846623294901874, 581816437168531777583991323662460237375659311104),
  (-1332376878874634819834390994001738993952160262378, -508428660160418146280495375065906003574125972288, 179854509644263896791744904561535746804316897280),
  (837895626616081745313036028024015937964225510305, -178100213431863011569641243694461526784648955926, -1184144530365309185986056276372037852756722057216),
  (1133760312559990497564353262778597878054340066809, 671483071479810965456562582319435846623294901874, -581816437168531777583991323662460237375659311104),
  (1332376878874634819834390994001738993952160262378, 508428660160418146280495375065906003574125972288, -179854509644263896791744904561535746804316897280),
  (-837895626616081745313036028024015937964225510305, -178100213431863011569641243694461526784648955926, 1184144530365309185986056276372037852756722057216),
  (-762624813218708840463060741640653496347691815001, -1074572173417503736085568558977187018900986797566, 581816437168531777583991323662460237375659311104),
  (-1010390279086773171342239258815713936491689194842, -1006399192050144629768594507558429959427050567192, 179854509644263896791744904561535746804316897280),
  (837895626616081745313036028024015937964225510305, 178100213431863011569641243694461526784648955926, -1184144530365309185986056276372037852756722057216),
  (762624813218708840463060741640653496347691815001, 1074572173417503736085568558977187018900986797566, -581816437168531777583991323662460237375659311104),
  (1010390279086773171342239258815713936491689194842, 1006399192050144629768594507558429959427050567192, -179854509644263896791744904561535746804316897280),
  (-693015860731362737831294890879271999188097043250, -503505495403575391382080051911658798266609398605, 1184144530365309185986056276372037852756722057216),
  (-259624555442986295470150540768519157301920420330, -1291857984389584521145944282452699990897244263205, 581816437168531777583991323662460237375659311104),
  (-513698020937288055399589381509284674323963472360, -1330354160784768183243678576898469875292046776210, 179854509644263896791744904561535746804316897280),
  (693015860731362737831294890879271999188097043250, 503505495403575391382080051911658798266609398605, -1184144530365309185986056276372037852756722057216),
  (259624555442986295470150540768519157301920420330, 1291857984389584521145944282452699990897244263205, -581816437168531777583991323662460237375659311104),
  (513698020937288055399589381509284674323963472360, 1330354160784768183243678576898469875292046776210, -179854509644263896791744904561535746804316897280),
  (-428307356674745733222990167388475941101552795648, -741850103016184513611710749990487004819930149958, 1184144530365309185986056276372037852756722057216),
  (288267146583869391339019130856359454970390540624, -1285769813699358173995868376756058447668135259510, 581816437168531777583991323662460237375659311104),
  (71817291832266784976976145538227604157036413448, -1424278809231573977542764597635737152815530207180, 179854509644263896791744904561535746804316897280),
  (428307356674745733222990167388475941101552795648, 741850103016184513611710749990487004819930149958, -1184144530365309185986056276372037852756722057216),
  (-288267146583869391339019130856359454970390540624, 1285769813699358173995868376756058447668135259510, -581816437168531777583991323662460237375659311104),
  (-71817291832266784976976145538227604157036413448, 1424278809231573977542764597635737152815530207180, -179854509644263896791744904561535746804316897280),
  (-89540619598883826499379453879423452277543225540, -851922088320686409438477687277413043920734976792, 1184144530365309185986056276372037852756722057216),
  (786314840141561652425658490232094202071234907228, -1057360361368459193579160233803740671054609745592, 581816437168531777583991323662460237375659311104),
  (644914742404408822342919538778354937836421060376, -1271932712395465629557373234566113844507084257504, 179854509644263896791744904561535746804316897280),
  (89540619598883826499379453879423452277543225540, 851922088320686409438477687277413043920734976792, -1184144530365309185986056276372037852756722057216),
  (-786314840141561652425658490232094202071234907228, 1057360361368459193579160233803740671054609745592, -581816437168531777583991323662460237375659311104),
  (-644914742404408822342919538778354937836421060376, 1271932712395465629557373234566113844507084257504, -179854509644263896791744904561535746804316897280),
  (264708504056617004608304723490796058086544247602, -814689005085338937022447060041603338324228316873, 1184144530365309185986056276372037852756722057216),
  (1148401554392713618421886452845200502512233167034, -646123696739631654940033228310023922965039640225, 581816437168531777583991323662460237375659311104),
  (1106500575148324669850405529028263181804357557168, -899657894440246649028354989902849797294289474010, 179854509644263896791744904561535746804316897280),
  (-264708504056617004608304723490796058086544247602, 814689005085338937022447060041603338324228316873, -1184144530365309185986056276372037852756722057216),
  (-1148401554392713618421886452845200502512233167034, 646123696739631654940033228310023922965039640225, -581816437168531777583991323662460237375659311104),
  (-1106500575148324669850405529028263181804357557168, 899657894440246649028354989902849797294289474010, -179854509644263896791744904561535746804316897280),
  (573187122559464740704731304533219879877681262703, -636588791653475925452805816347141811539579360947, 1184144530365309185986056276372037852756722057216),
  (1311919206988769922094620235687870649392305739151, -123166375095012559128621550199507706831488582275, 581816437168531777583991323662460237375659311104),
  (1376762406206945905190672548358833851681451819202, -371824053400922076027002350743242745732117403890, 179854509644263896791744904561535746804316897280),
  (-573187122559464740704731304533219879877681262703, 636588791653475925452805816347141811539579360947, -1184144530365309185986056276372037852756722057216),
  (-1311919206988769922094620235687870649392305739151, 123166375095012559128621550199507706831488582275, -581816437168531777583991323662460237375659311104),
  (-1376762406206945905190672548358833851681451819202, 371824053400922076027002350743242745732117403890, -179854509644263896791744904561535746804316897280),
  (782556480330246564330675053333778761834204556661, -348416592917111018056397635365754245654125578187, 1184144530365309185986056276372037852756722057216),
  (1248594110284634120748530844990623082416133191429, 421087531734924675576628706803698423964660368117, 581816437168531777583991323662460237375659311104),
  (1408969509738580907457471946155430748480715336238, 220301544386902185328074669951108462734669843174, 179854509644263896791744904561535746804316897280),
  (-782556480330246564330675053333778761834204556661, 348416592917111018056397635365754245654125578187, -1184144530365309185986056276372037852756722057216),
  (-1248594110284634120748530844990623082416133191429, -421087531734924675576628706803698423964660368117, -581816437168531777583991323662460237375659311104),
  (-1408969509738580907457471946155430748480715336238, -220301544386902185328074669951108462734669843174, -179854509644263896791744904561535746804316897280)
]

/-- The vertices with their indices and coordinate absolute values. -/
def vtxIdx : List (Nat × (Int × Int × Int) × (Int × Int × Int)) :=
  (List.range 90).zip (vtxI.map fun (x, y, z) => ((x, y, z), ((x.natAbs : Int), (y.natAbs : Int), (z.natAbs : Int))))

/-- The sign bits of the packed slots, `Σ_T 2^(640 T + 639)`. -/
def signT : Nat := Nat.shiftLeft onesT 639

/-- Coordinate `t` of a packed table, `(tab >>> 640 t) mod 2^640`. -/
def slot (tab t : Nat) : Int := ((Nat.land (Nat.shiftRight tab (640 * t)) (2 ^ 640 - 1) : Nat) : Int)

/-- Run `f` on every vertex `lo + i` (`i < n`) whose slot bit `640 i + 639` is set in `m`,
by binary splitting (`depth` bounds the recursion). -/
def vtxSplit (f : Nat → Int → Int → Int → Int → Int → Int → Bool) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, m => m == 0
  | depth + 1, lo, n, m =>
    if m == 0 then true
    else if n ≤ 1 then
      let B : Int := ((2 ^ 170 : Nat) : Int)
      f lo (slot tpx lo - B) (slot tpy lo - B) (slot tpz lo - B)
        (B - slot tax lo) (B - slot tay lo) (B - slot taz lo)
    else
      let h := n / 2
      vtxSplit f depth lo h (Nat.land m (2 ^ (640 * h) - 1)) &&
        vtxSplit f depth (lo + h) (n - h) (Nat.shiftRight m (640 * h))

/-- `2^k` as an integer. -/
def p2 (k : Nat) : Int := ((2 ^ k : Nat) : Int)

/-- The chart base `M_j` (integer entries; `B_j = M_j / κ_j`). -/
def chartMI : Nat → Int × Int × Int × Int × Int × Int × Int × Int × Int
  | 0 => (1, 0, 0, 0, 1, 0, 0, 0, 1)
  | 1 => (1, 0, 0, 0, -1, 0, 0, 0, -1)
  | 2 => (-1, 0, 0, 0, 1, 0, 0, 0, -1)
  | 3 => (-1, 0, 0, 0, -1, 0, 0, 0, 1)
  | _ => (-(c3x * c3x - c3y * c3y), -(2 * c3x * c3y), 0, -(2 * c3x * c3y), c3x * c3x - c3y * c3y, 0,
          0, 0, -kappaTau)

def chartKI : Nat → Int
  | 4 => kappaTau
  | _ => 1

/-- `M v` on `S9` triples for the chart base `M_j`. -/
def chartMS (chart : Nat) (y0 y1 y2 : S9) : S9 × S9 × S9 :=
  match chart with
  | 0 => (y0, y1, y2)
  | 1 => (y0, y1.smul (-1), y2.smul (-1))
  | 2 => (y0.smul (-1), y1, y2.smul (-1))
  | 3 => (y0.smul (-1), y1.smul (-1), y2)
  | _ =>
    let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := chartMI 4
    (((y0.smul m00).add (y1.smul m01)).add (y2.smul m02),
     ((y0.smul m10).add (y1.smul m11)).add (y2.smul m12),
     ((y0.smul m20).add (y1.smul m21)).add (y2.smul m22))

/-- `M v` for a constant integer matrix and three polynomials. -/
def mulMY (M : Int × Int × Int × Int × Int × Int × Int × Int × Int) (y0 y1 y2 : Y27) :
    Y27 × Y27 × Y27 :=
  let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := M
  (((y0.smul m00).add (y1.smul m01)).add (y2.smul m02),
   ((y0.smul m10).add (y1.smul m11)).add (y2.smul m12),
   ((y0.smul m20).add (y1.smul m21)).add (y2.smul m22))

/-- `M v` for the chart base `M_j`: the Klein charts are diagonal sign flips. -/
def chartMY (chart : Nat) (y0 y1 y2 : Y27) : Y27 × Y27 × Y27 :=
  match chart with
  | 0 => (y0, y1, y2)
  | 1 => (y0, y1.smul (-1), y2.smul (-1))
  | 2 => (y0.smul (-1), y1, y2.smul (-1))
  | 3 => (y0.smul (-1), y1.smul (-1), y2)
  | _ => mulMY (chartMI 4) y0 y1 y2

def X6.absSum (a : X6) : Int := (a.f0).natAbs + a.slack
def Y27.absSum (a : Y27) : Int := (a.f0).natAbs + a.slack

/-- The per-box polynomials: `α` (outer rows, needs `w`), `β = M N(r) S`, `κD`, and for the
blown-up charts the paired-vertex inner vector `M (U² c×S + ρ c×(c×S))`. -/
structure KData where
  a0 : X6
  a1 : X6
  a2 : X6
  b0 : Y27
  b1 : Y27
  b2 : Y27
  kd : Y27
  /-- scale exponent of `Σ αₖ βₖ` beyond `2^160` -/
  sc : Nat
  l0 : Y27
  l1 : Y27
  l2 : Y27
  scL : Nat

def gapData (b : KBox) (S : Int × Int × Int) (w0 w1 : Int) : KData :=
  let K := b.K
  let U := p2 K
  let U2 := U * U
  let cu := b.c.getD 0 0
  let hu := b.h.getD 0 0
  let cv := b.c.getD 1 0
  let hv := b.h.getD 1 0
  let u : X6 := ⟨cu, hu, 0, 0, 0, 0⟩
  let v : X6 := ⟨cv, 0, hv, 0, 0, 0⟩
  let uu := u.mulLin u
  let vv := v.mulLin v
  let uv := u.mulLin v
  let one2 : X6 := ⟨U2, 0, 0, 0, 0, 0⟩
  -- rows 0, 1 of N(v, -u, 0) · U²
  let n00 := (one2.add vv).sub uu
  let n01 := uv.smul (-2)
  let n02 := u.smul (-2 * U)
  let n11 := (one2.sub vv).add uu
  let n12 := v.smul (-2 * U)
  let a0 := (n00.smul w0).add (n01.smul w1)
  let a1 := (n01.smul w0).add (n11.smul w1)
  let a2 := (n02.smul w0).add (n12.smul w1)
  let (sx, sy, sz) := S
  let κ := chartKI b.chart
  if b.chart = 0 ∨ b.chart = 4 then
    -- blown up: r = ρ c, c on cube face, all over U
    let sg : Int := if b.face % 2 = 0 then U else -U
    let s0 : S9 := ⟨b.c.getD 2 0, b.h.getD 2 0, 0, 0, 0, 0, 0, 0, 0⟩
    let s1 : S9 := ⟨b.c.getD 3 0, 0, 0, b.h.getD 3 0, 0, 0, 0, 0, 0⟩
    let cst : S9 := ⟨sg, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let (cx, cy, cz) : S9 × S9 × S9 :=
      if b.face / 2 = 0 then (cst, s0, s1) else if b.face / 2 = 1 then (s1, cst, s0) else (s0, s1, cst)
    let ρ : R3 := ⟨b.c.getD 4 0, b.h.getD 4 0, 0⟩
    let ρ2 : R3 := ⟨ρ.f0 * ρ.f0, 2 * ρ.f0 * ρ.f1, ρ.f1 * ρ.f1⟩
    let one : R3 := ⟨1, 0, 0⟩
    let c2 := ((cx.mulLin cx).add (cy.mulLin cy)).add (cz.mulLin cz)
    let cS := ((cx.smul sx).add (cy.smul sy)).add (cz.smul sz)
    let cxS : S9 × S9 × S9 := ((cy.smul sz).sub (cz.smul sy), (cz.smul sx).sub (cx.smul sz),
      (cx.smul sy).sub (cy.smul sx))
    let U4 := U2 * U2
    let (x0, x1, x2) := cxS
    -- N(ρc)S = S·U⁴ ⊗ 1 + (2 c(c·S) − |c|² S) ⊗ ρ² + 2U² (c×S) ⊗ ρ, combined with M before the
    -- outer products
    let p0 : S9 := ⟨Int.mul sx U4, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let p1 : S9 := ⟨Int.mul sy U4, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let p2' : S9 := ⟨Int.mul sz U4, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let q0 := ((cx.mulLin cS).smul 2).sub (c2.smul sx)
    let q1 := ((cy.mulLin cS).smul 2).sub (c2.smul sy)
    let q2 := ((cz.mulLin cS).smul 2).sub (c2.smul sz)
    let r0 := x0.smul (2 * U2)
    let r1 := x1.smul (2 * U2)
    let r2 := x2.smul (2 * U2)
    let (P0, P1, P2) := chartMS b.chart p0 p1 p2'
    let (Q0, Q1, Q2) := chartMS b.chart q0 q1 q2
    let (R0, R1, R2) := chartMS b.chart r0 r1 r2
    let bk (P Q R : S9) : Y27 := ((S9.outerR P one).add (S9.outerR Q ρ2)).add (S9.outerR R ρ)
    let b0 := bk P0 Q0 R0
    let b1 := bk P1 Q1 R1
    let b2 := bk P2 Q2 R2
    let d := (S9.outerR ⟨U4, 0, 0, 0, 0, 0, 0, 0, 0⟩ one).add (S9.outerR c2 ρ2)
    -- paired inner vector U² (c×S) + ρ c×(c×S), over U³
    let ccx : S9 × S9 × S9 := ((cy.mulLin x2).sub (cz.mulLin x1), (cz.mulLin x0).sub (cx.mulLin x2),
      (cx.mulLin x1).sub (cy.mulLin x0))
    let (k0, k1, k2) := ccx
    let (X0, X1, X2) := chartMS b.chart (x0.smul U2) (x1.smul U2) (x2.smul U2)
    let (K0, K1, K2) := chartMS b.chart k0 k1 k2
    let l0 := (S9.outerR X0 one).add (S9.outerR K0 ρ)
    let l1 := (S9.outerR X1 one).add (S9.outerR K1 ρ)
    let l2 := (S9.outerR X2 one).add (S9.outerR K2 ρ)
    { a0, a1, a2, b0, b1, b2, kd := d.smul κ, sc := 6 * K, l0, l1, l2, scL := 5 * K }
  else
    -- plain chart: r affine in t₂, t₃, t₄, over U
    let r0 : Y27 := ⟨b.c.getD 2 0, b.h.getD 2 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let r1 : Y27 := ⟨b.c.getD 3 0, 0, 0, b.h.getD 3 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let r2 : Y27 := ⟨b.c.getD 4 0, 0, 0, 0, 0, 0, 0, 0, 0, b.h.getD 4 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let r2s := ((r0.mulLin r0).add (r1.mulLin r1)).add (r2.mulLin r2)
    let rS := ((r0.smul sx).add (r1.smul sy)).add (r2.smul sz)
    let oneU2 : Y27 := ⟨U2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let nrs (si : Int) (ri : Y27) (rxi : Y27) : Y27 :=
      (((oneU2.sub r2s).smul si).add ((ri.mulLin rS).smul 2)).add (rxi.smul (2 * U))
    let n0 := nrs sx r0 ((r1.smul sz).sub (r2.smul sy))
    let n1 := nrs sy r1 ((r2.smul sx).sub (r0.smul sz))
    let n2 := nrs sz r2 ((r0.smul sy).sub (r1.smul sx))
    let (b0, b1, b2) := chartMY b.chart n0 n1 n2
    { a0, a1, a2, b0, b1, b2, kd := (oneU2.add r2s).smul κ, sc := 4 * K,
      l0 := Y27.zero, l1 := Y27.zero, l2 := Y27.zero, scL := 0 }

/-- The paired vertex for the blown-up charts. -/
def kPair (chart j : Nat) : Option Nat := pairOf chart j

/-- Kernel gap leaf. -/
def kGapOK (b : KBox) (s : Nat) (w0 w1 : Int) : Bool :=
  if s < 90 then
    let S := vtxI.getD s (0, 0, 0)
    let g := gapData b S w0 w1
    let κ := chartKI b.chart
    let W : Int := w0.natAbs + w1.natAbs
    let err : Int := 128 * κ * W * p2 (g.sc + 100)
    let AB := prod3 g.a0 g.a1 g.a2 g.b0 g.b1 g.b2
    let A := statsB AB
    let aS : Int := A.l0.natAbs + A.l1.natAbs + A.l2.natAbs + A.l3.natAbs + A.l4.natAbs + A.nl
    let kdS := g.kd.absSum
    let e0 (a : X6) : Int := a.f0 * g.kd.f0
    let eS (a : X6) : Int := a.absSum * kdS - (e0 a).natAbs
    let e00 := e0 g.a0
    let e01 := e0 g.a1
    let e02 := e0 g.a2
    let eS0 := eS g.a0
    let eS1 := eS g.a1
    let eS2 := eS g.a2
    let pr := if b.chart = 0 ∨ b.chart = 4 then kPair b.chart s else none
    let errL := 128 * κ * W * p2 (g.scL + 100)
    let qL (a : X6) (m : Y27) : Int := a.f0 * m.f0 - (a.absSum * m.absSum - (a.f0 * m.f0).natAbs)
    -- does the box touch ρ = 0 (blown-up charts)?
    let touches : Bool := decide (b.c.getD 4 0 - b.h.getD 4 0 ≤ 0)
    -- packed quick test: slot t of V is 2^639 + quick_t (when the packing bounds hold)
    let B : Int := p2 170
    let C : Int := p2 639 + (A.c0 - aS - err) -
      B * (((e00.natAbs : Int) + e01.natAbs + e02.natAbs) + (eS0 + eS1 + eS2))
    let packOK : Bool := decide (0 ≤ C) &&
      decide (C + 2 * B * (((e00.natAbs : Int) + e01.natAbs + e02.natAbs) + (eS0 + eS1 + eS2)) < p2 640)
    let tab (e : Int) (tn tp : Nat) : Nat := Nat.mul e.natAbs (if 0 ≤ e then tn else tp)
    let V : Nat := Nat.add (Nat.add (Nat.add (Nat.mul C.toNat onesT) (tab e00 tnx tpx))
      (Nat.add (tab e01 tny tpy) (tab e02 tnz tpz)))
      (Nat.add (Nat.mul eS0.toNat tax) (Nat.add (Nat.mul eS1.toNat tay) (Nat.mul eS2.toNat taz)))
    -- the scalar quick, linear and full tests against outer vertex `T`
    let rest (tx ty tz ax ay az : Int) : Bool :=
      let c0 := A.c0 - (tx * e00 + ty * e01 + tz * e02)
      let quick := c0 - (aS + ax * eS0 + ay * eS1 + az * eS2)
      (!packOK && decide (err ≤ quick)) ||
        (let x := ((g.a0.smul tx).add (g.a1.smul ty)).add (g.a2.smul tz)
         let k := g.kd
         let el0 := x.f1 * k.f0
         let el1 := x.f2 * k.f0
         let el2 := x.f0 * k.f1
         let el3 := x.f0 * k.f3
         let el4 := x.f0 * k.f9
         let ec := x.f0 * k.f0
         let enl := x.absSum * kdS - ec.natAbs - el0.natAbs - el1.natAbs - el2.natAbs -
           el3.natAbs - el4.natAbs
         let lin : Int := (A.l0 - el0).natAbs + (A.l1 - el1).natAbs + (A.l2 - el2).natAbs +
           (A.l3 - el3).natAbs + (A.l4 - el4).natAbs
         decide (err ≤ c0 - lin - (A.nl + enl)) ||
           decide (err ≤ fullLowerB AB x g.kd))
    let vtest (t : Nat) (tx ty tz ax ay az : Int) : Bool :=
      if pr = some t then
        -- the paired vertex: the divided test `L ≥ 0`, or the plain tests away from ρ = 0
        decide (errL ≤ 2 * (qL g.a0 g.l0 + qL g.a1 g.l1 + qL g.a2 g.l2)) ||
          (!touches && rest tx ty tz ax ay az) ||
          decide (errL ≤ 2 * lower3 g.a0 g.a1 g.a2 g.l0 g.l1 g.l2)
      else rest tx ty tz ax ay az
    (w0 != 0 || w1 != 0) &&
      if packOK then
        -- the vertices whose packed quick test failed
        let fails : Nat := Nat.xor signT (Nat.land V signT)
        vtxSplit vtest 8 0 90 fails
      else vtxIdx.all fun (t, (tx, ty, tz), (ax, ay, az)) => vtest t tx ty tz ax ay az
  else false

/-- The Cayley numerator `N(r)` (all nine entries) as `Y27` polynomials, over `R²` where `R` is
the scale of `r` (`U²` blown up, `U` plain), and `R²` itself. -/
def numMatrix (b : KBox) : (Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27) × Int × Y27 :=
  let U := p2 b.K
  let U2 := U * U
  if b.chart = 0 ∨ b.chart = 4 then
    let sg : Int := if b.face % 2 = 0 then U else -U
    let s0 : S9 := ⟨b.c.getD 2 0, b.h.getD 2 0, 0, 0, 0, 0, 0, 0, 0⟩
    let s1 : S9 := ⟨b.c.getD 3 0, 0, 0, b.h.getD 3 0, 0, 0, 0, 0, 0⟩
    let cst : S9 := ⟨sg, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let (cx, cy, cz) : S9 × S9 × S9 :=
      if b.face / 2 = 0 then (cst, s0, s1) else if b.face / 2 = 1 then (s1, cst, s0) else (s0, s1, cst)
    let ρ : R3 := ⟨b.c.getD 4 0, b.h.getD 4 0, 0⟩
    let ρ2 : R3 := ⟨ρ.f0 * ρ.f0, 2 * ρ.f0 * ρ.f1, ρ.f1 * ρ.f1⟩
    let one : R3 := ⟨1, 0, 0⟩
    let c2 := ((cx.mulLin cx).add (cy.mulLin cy)).add (cz.mulLin cz)
    let U4 := U2 * U2
    let dg (ca : S9) : Y27 :=
      (S9.outerR ⟨U4, 0, 0, 0, 0, 0, 0, 0, 0⟩ one).add (S9.outerR (((ca.mulLin ca).smul 2).sub c2) ρ2)
    let od (ca cb cc : S9) (sgn : Int) : Y27 :=
      (S9.outerR ((ca.mulLin cb).smul 2) ρ2).add (S9.outerR (cc.smul (sgn * 2 * U2)) ρ)
    -- N = (1 - |r|²) I + 2 r rᵀ + 2 [r]×, [r]× = !![0, -z, y; z, 0, -x; -y, x, 0]
    ((dg cx, od cx cy cz (-1), od cx cz cy 1,
      od cy cx cz 1, dg cy, od cy cz cx (-1),
      od cz cx cy (-1), od cz cy cx 1, dg cz), U4,
      (S9.outerR ⟨U4, 0, 0, 0, 0, 0, 0, 0, 0⟩ one).add (S9.outerR c2 ρ2))
  else
    let r0 : Y27 := ⟨b.c.getD 2 0, b.h.getD 2 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let r1 : Y27 := ⟨b.c.getD 3 0, 0, 0, b.h.getD 3 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let r2 : Y27 := ⟨b.c.getD 4 0, 0, 0, 0, 0, 0, 0, 0, 0, b.h.getD 4 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let r2s := ((r0.mulLin r0).add (r1.mulLin r1)).add (r2.mulLin r2)
    let oneU2 : Y27 := ⟨U2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let dg (ra : Y27) : Y27 := (oneU2.sub r2s).add ((ra.mulLin ra).smul 2)
    let od (ra rb rc : Y27) (sgn : Int) : Y27 := ((ra.mulLin rb).smul 2).add (rc.smul (sgn * 2 * U))
    ((dg r0, od r0 r1 r2 (-1), od r0 r2 r1 1,
      od r1 r0 r2 1, dg r1, od r1 r2 r0 (-1),
      od r2 r0 r1 (-1), od r2 r1 r0 1, dg r2), U2, oneU2.add r2s)

/-- `tr(Xᵀ N) = Σ X_ab N_ab` for an integer matrix `X`. -/
def trTN (X : Int × Int × Int × Int × Int × Int × Int × Int × Int)
    (N : Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27) : Y27 :=
  let (x00, x01, x02, x10, x11, x12, x20, x21, x22) := X
  let (n00, n01, n02, n10, n11, n12, n20, n21, n22) := N
  ((((((((n00.smul x00).add (n01.smul x01)).add (n02.smul x02)).add (n10.smul x10)).add
    (n11.smul x11)).add (n12.smul x12)).add (n20.smul x20)).add (n21.smul x21)).add (n22.smul x22)

/-- `Aᵀ B` for integer matrices. -/
def mtm (A B : Int × Int × Int × Int × Int × Int × Int × Int × Int) :
    Int × Int × Int × Int × Int × Int × Int × Int × Int :=
  let (a00, a01, a02, a10, a11, a12, a20, a21, a22) := A
  let (b00, b01, b02, b10, b11, b12, b20, b21, b22) := B
  (a00 * b00 + a10 * b10 + a20 * b20, a00 * b01 + a10 * b11 + a20 * b21, a00 * b02 + a10 * b12 + a20 * b22,
   a01 * b00 + a11 * b10 + a21 * b20, a01 * b01 + a11 * b11 + a21 * b21, a01 * b02 + a11 * b12 + a21 * b22,
   a02 * b00 + a12 * b10 + a22 * b20, a02 * b01 + a12 * b11 + a22 * b21, a02 * b02 + a12 * b12 + a22 * b22)

/-- Kernel chart test: chart `k` beats the box's chart `j` on the whole box,
`κ_j tr(M_kᵀ M_j N) > κ_k tr(M_jᵀ M_j N)`. -/
def kChartOK (b : KBox) (k : Nat) : Bool :=
  let (N, _, _) := numMatrix b
  let j := b.chart
  let Mj := chartMI j
  let d := (trTN (mtm Mj (chartMI k)) N).smul (chartKI j) |>.sub
    ((trTN (mtm Mj Mj) N).smul (chartKI k))
  decide (0 < d.lower)

/-- `M N` for an integer matrix and a polynomial matrix. -/
def mulMN (M : Int × Int × Int × Int × Int × Int × Int × Int × Int)
    (N : Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27) :
    Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 × Y27 :=
  let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := M
  let (n00, n01, n02, n10, n11, n12, n20, n21, n22) := N
  let e (a0 a1 a2 : Int) (x0 x1 x2 : Y27) : Y27 := ((x0.smul a0).add (x1.smul a1)).add (x2.smul a2)
  (e m00 m01 m02 n00 n10 n20, e m00 m01 m02 n01 n11 n21, e m00 m01 m02 n02 n12 n22,
   e m10 m11 m12 n00 n10 n20, e m10 m11 m12 n01 n11 n21, e m10 m11 m12 n02 n12 n22,
   e m20 m21 m22 n00 n10 n20, e m20 m21 m22 n01 n11 n21, e m20 m21 m22 n02 n12 n22)

/-- Integer matrix product. -/
def mmI (A B : Int × Int × Int × Int × Int × Int × Int × Int × Int) :
    Int × Int × Int × Int × Int × Int × Int × Int × Int :=
  let (a00, a01, a02, a10, a11, a12, a20, a21, a22) := A
  let (b00, b01, b02, b10, b11, b12, b20, b21, b22) := B
  (a00 * b00 + a01 * b10 + a02 * b20, a00 * b01 + a01 * b11 + a02 * b21, a00 * b02 + a01 * b12 + a02 * b22,
   a10 * b00 + a11 * b10 + a12 * b20, a10 * b01 + a11 * b11 + a12 * b21, a10 * b02 + a11 * b12 + a12 * b22,
   a20 * b00 + a21 * b10 + a22 * b20, a20 * b01 + a21 * b11 + a22 * b21, a20 * b02 + a21 * b12 + a22 * b22)

/-- Kernel orbit test: the orbit element `H^e Q ĝ_g` (score base `a`) beats `Q`. -/
def kOrbitOK (b : KBox) (e g a : Nat) : Bool :=
  let (N, R2, D) := numMatrix b
  let j := b.chart
  let Mj := chartMI j
  let κj := chartKI j
  let κ4 := kappaTau
  let c := (cosTab.getD g 0).m
  let s := (sinTab.getD g 0).m
  let G80 := p2 80
  let C := mmI (chartMI a) (c, s, 0, -s, c, 0, 0, 0, G80)
  let fa : Int := if a = 4 then 1 else κ4
  let tr0 := trTN (mtm Mj (chartMI 0)) N
  let tr4 := trTN (mtm Mj (chartMI 4)) N
  let dsh := D.smul (κ4 * κj * p2 77)
  if e = 0 then
    let sx := (trTN (mtm Mj C) N).smul fa
    let sx := if a = 4 then sx.sub dsh else sx
    let err := 128 * κ4 * κj * R2 * p2 20
    decide (err < (sx.sub (tr0.smul (κ4 * G80))).lower) &&
      decide (err < (sx.sub ((tr4.smul G80).sub dsh)).lower)
  else
    let U := p2 b.K
    let U2 := U * U
    let cu := b.c.getD 0 0
    let hu := b.h.getD 0 0
    let cv := b.c.getD 1 0
    let hv := b.h.getD 1 0
    let u : X6 := ⟨cu, hu, 0, 0, 0, 0⟩
    let v : X6 := ⟨cv, 0, hv, 0, 0, 0⟩
    let uu := u.mulLin u
    let vv := v.mulLin v
    let uv := u.mulLin v
    let one2 : X6 := ⟨U2, 0, 0, 0, 0, 0⟩
    let n00 := (one2.add vv).sub uu
    let n01 := uv.smul (-2)
    let n02 := u.smul (-2 * U)
    let n11 := (one2.sub vv).add uu
    let n12 := v.smul (-2 * U)
    let n20 := u.smul (2 * U)
    let n21 := v.smul (2 * U)
    let n22 := (one2.sub vv).sub uu
    -- H = N_oᵀ diag(-1,-1,1) N_o (over U⁴), symmetric
    let hab (x0 y0 x1 y1 x2 y2 : X6) : X15 := ((x2.mulX y2).sub (x0.mulX y0)).sub (x1.mulX y1)
    let h00 := hab n00 n00 n01 n01 n20 n20
    let h01 := hab n00 n01 n01 n11 n20 n21
    let h02 := hab n00 n02 n01 n12 n20 n22
    let h11 := hab n01 n01 n11 n11 n21 n21
    let h12 := hab n01 n02 n11 n12 n21 n22
    let h22 := hab n02 n02 n12 n12 n22 n22
    -- W = C Pᵀ with P = M_j N; Σ_ab H_ab W_ab, off-diagonals folded
    let P := mulMN Mj N
    let (c00, c01, c02, c10, c11, c12, c20, c21, c22) := C
    let (p00, p01, p02, p10, p11, p12, p20, p21, p22) := P
    let wab (ca0 ca1 ca2 : Int) (pb0 pb1 pb2 : Y27) : Y27 :=
      ((pb0.smul ca0).add (pb1.smul ca1)).add (pb2.smul ca2)
    let w00 := wab c00 c01 c02 p00 p01 p02
    let w01 := wab c00 c01 c02 p10 p11 p12
    let w02 := wab c00 c01 c02 p20 p21 p22
    let w10 := wab c10 c11 c12 p00 p01 p02
    let w11 := wab c10 c11 c12 p10 p11 p12
    let w12 := wab c10 c11 c12 p20 p21 p22
    let w20 := wab c20 c21 c22 p00 p01 p02
    let w21 := wab c20 c21 c22 p10 p11 p12
    let w22 := wab c20 c21 c22 p20 p21 p22
    let T := prod6H h00 h01 h02 h11 h12 h22 (w00.smul fa) ((w01.add w10).smul fa) ((w02.add w20).smul fa)
      (w11.smul fa) ((w12.add w21).smul fa) (w22.smul fa)
    let dO := (one2.add uu).add vv
    let do2 := dO.mulX dO
    let ash := if a = 4 then dsh else Y27.zero
    let err := 1024 * κ4 * κj * U2 * U2 * R2 * p2 20
    decide (err < lowerH T do2 (ash.add (tr0.smul (κ4 * G80)))) &&
      decide (err < lowerH T do2 (ash.add ((tr4.smul G80).sub dsh)))

/-- Convert a kernel box back to a checker box. -/
def toBox (b : KBox) : Box :=
  { chart := b.chart, face := b.face,
    c := ⟨#[QI.mk (b.c.getD 0 0) b.K, QI.mk (b.c.getD 1 0) b.K, QI.mk (b.c.getD 2 0) b.K,
      QI.mk (b.c.getD 3 0) b.K, QI.mk (b.c.getD 4 0) b.K], rfl⟩,
    h := ⟨#[QI.mk (b.h.getD 0 0) b.K, QI.mk (b.h.getD 1 0) b.K, QI.mk (b.h.getD 2 0) b.K,
      QI.mk (b.h.getD 3 0) b.K, QI.mk (b.h.getD 4 0) b.K], rfl⟩ }

/-- Kernel domain leaf. -/
def kDomOK (b : KBox) (code : Nat) : Bool :=
  let U := p2 b.K
  if code = 0 then
    let ulo := b.c.getD 0 0 - b.h.getD 0 0
    let vlo := b.c.getD 1 0 - b.h.getD 1 0
    decide (0 ≤ ulo) && decide (0 ≤ vlo) && decide (U * U < ulo * ulo + vlo * vlo)
  else if code = 1 then
    let uhi := b.c.getD 0 0 + b.h.getD 0 0
    let vlo := b.c.getD 1 0 - b.h.getD 1 0
    decide (0 ≤ uhi) && decide (57 * uhi < 128 * vlo)
  else if code < 7 then kChartOK b (code - 2)
  else if code < 67 then
    let i := code - 7
    kOrbitOK b (i / 30) (i / 2 % 15) (if i % 2 = 0 then 0 else 4)
  else false

/-- X6 slot degrees and Y27 slot degrees. -/
def x6deg (i : Nat) : Nat := if i = 0 then 0 else if i ≤ 2 then 1 else 2
def y27deg (j : Nat) : Nat := j % 3 + j / 3 % 3 + j / 9

def X6.toList (a : X6) : List Int := [a.f0, a.f1, a.f2, a.f3, a.f4, a.f5]
def Y27.toList (a : Y27) : List Int :=
  [a.f0, a.f1, a.f2, a.f3, a.f4, a.f5, a.f6, a.f7, a.f8, a.f9, a.f10, a.f11, a.f12, a.f13, a.f14,
   a.f15, a.f16, a.f17, a.f18, a.f19, a.f20, a.f21, a.f22, a.f23, a.f24, a.f25, a.f26]

/-- Experimental (native only): lower bound of `Σₖ αₖ ⊗ (βₖ − κ Tₖ D)` with exact
coefficients up to degree 2 and a triangle bound for degree ≥ 3. -/
def quadBound (g : KData) (tx ty tz : Int) : Int := Id.run do
  let γ := [g.b0.sub (g.kd.smul tx), g.b1.sub (g.kd.smul ty), g.b2.sub (g.kd.smul tz)]
  let α := [g.a0, g.a1, g.a2]
  let mut low : Int := 0
  -- exact low-degree coefficients
  for i in [0:6] do
    for j in [0:27] do
      let d := x6deg i + y27deg j
      if d ≤ 2 then
        let mut v : Int := 0
        for k in [0:3] do
          v := v + ((α.getD k X6.zero).toList.getD i 0) * ((γ.getD k Y27.zero).toList.getD j 0)
        let ex := (if i = 3 ∨ i = 5 then [2, 0] else if i = 1 then [1, 0] else if i = 2 then [0, 1] else if i = 4 then [1, 1] else [0, 0])
        let ey := [j % 3, j / 3 % 3, j / 9]
        let even := (ex ++ ey).all (· % 2 = 0)
        if d = 0 then low := low + v
        else if even then low := low + min 0 v
        else low := low - v.natAbs
  -- triangle bound for degree ≥ 3
  for k in [0:3] do
    let a := (α.getD k X6.zero).toList
    let b := (γ.getD k Y27.zero).toList
    for i in [0:6] do
      for j in [0:27] do
        if x6deg i + y27deg j ≥ 3 then low := low - ((a.getD i 0) * (b.getD j 0)).natAbs
  return low

/-- Convert a checker box (dyadic coordinates) to integers over a common `2^K`. -/
def ofBox (b : Box) : KBox :=
  let K := (b.c.toList ++ b.h.toList).foldr (fun q acc => max q.e acc) 0
  let conv (q : QI) : Int := q.m * p2 (K - q.e)
  { chart := b.chart, face := b.face, K, c := b.c.toList.map conv, h := b.h.toList.map conv }

end Cayley.K

end
