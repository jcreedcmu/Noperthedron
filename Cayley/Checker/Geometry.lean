module

public import Cayley.Checker.QI

@[expose] public section

/-!
# Exact data for the Cayley checker

Dyadic approximations (error at most `2⁻⁶⁰` per coordinate) of the Noperthedron
vertices and of the symmetry rotations `Rz(2πk/15)`, the half-turn `τ` data, and the
paired vertices of the blown-up charts. Mathlib-free.
-/

namespace Cayley

/-- Three-vectors. -/
structure V3 (α : Type) where
  x : α
  y : α
  z : α
deriving Inhabited

/-- 3×3 matrices, stored by entries so that compiled code never recomputes them. -/
structure M3 (α : Type) where
  a00 : α
  a01 : α
  a02 : α
  a10 : α
  a11 : α
  a12 : α
  a20 : α
  a21 : α
  a22 : α
deriving Inhabited

/-- The dyadic number `m · 2⁻⁸⁰`. -/
def d80 (m : Int) : QI := QI.mk m 80

/-- `cos(2πk/15)` to within `2⁻⁸⁰`. -/
def cosTab : Array QI := #[
  d80 1208925819614629174706176, d80 1104408691135802787572491, d80 808929266721616466411793,
  d80 373578623199582567987662, d80 (-126367158128905632231740), d80 (-604462909807314587353088),
  d80 (-978041533006897155340750), d80 (-1182507889921199034399455), d80 (-1182507889921199034399455),
  d80 (-978041533006897155340750), d80 (-604462909807314587353088), d80 (-126367158128905632231740),
  d80 373578623199582567987662, d80 808929266721616466411793, d80 1104408691135802787572491]

/-- `sin(2πk/15)` to within `2⁻⁸⁰`. -/
def sinTab : Array QI := #[
  d80 0, d80 491714429597714652495797, d80 898406967232629382321357,
  d80 1149756778461952459611063, d80 1202303197482784322232552, d80 1046960471077192669696698,
  d80 710588767885069669736755, d80 251349811229323077289706, d80 (-251349811229323077289706),
  d80 (-710588767885069669736755), d80 (-1046960471077192669696698), d80 (-1202303197482784322232552),
  d80 (-1149756778461952459611063), d80 (-898406967232629382321357), d80 (-491714429597714652495797)]

/-- The points `C1, C2, C3` to within `2⁻⁸⁰`. -/
def cTab : Array (V3 QI) := #[
  ⟨d80 708575083310368564287871, d80 0, d80 979501397978893732372791⟩,
  ⟨d80 801848825678901923219191, d80 738284818130756748970184, d80 481267276890486254372654⟩,
  ⟨d80 990592611655862735853342, d80 640514902742640119587028, d80 148772163457966633721405⟩]

/-- Vertex `6k + 3ℓ + i` is `(-1)^ℓ Rz(2πk/15) C_i`. -/
def vertexOf (k l i : Nat) : V3 QI :=
  let c := cosTab[k]!
  let s := sinTab[k]!
  let p := cTab[i]!
  let v : V3 QI := ⟨c * p.x - s * p.y, s * p.x + c * p.y, p.z⟩
  if l = 0 then v else ⟨-v.x, -v.y, -v.z⟩

def vertexTab : Array (V3 QI) :=
  (Array.range 90).map fun j => vertexOf (j / 6) (j % 6 / 3) (j % 3)

/-- `Rz(2πk/15)` approximately. -/
def groupTab : Array (M3 QI) :=
  (Array.range 15).map fun k =>
    let c := cosTab[k]!
    let s := sinTab[k]!
    ⟨c, -s, 0, s, c, 0, 0, 0, 1⟩

/-- `C3 = (x', y', ·) · 10⁻¹⁰`. -/
def c3x : Int := 8193990033
def c3y : Int := 5298215096

/-- The denominator `κ = x'² + y'²` of the half-turn `τ`. -/
def kappaTau : Int := c3x * c3x + c3y * c3y

/-- The vertex that `τ` maps vertex `j` to, for the 30 copies of `C3`. -/
def tauPair (j : Nat) : Option Nat :=
  if j % 3 = 2 then
    let k := j / 6
    let l := j % 6 / 3
    some (6 * ((15 - k) % 15) + 3 * (1 - l) + 2)
  else none

/-- The paired vertex for the blown-up charts. -/
def pairOf (chart j : Nat) : Option Nat :=
  if chart = 0 then some j else if chart = 4 then tauPair j else none

/-- Componentwise error bound `ε = 2⁻⁶⁰` of the approximations. -/
def errε : QI := QI.mk 1 60

end Cayley

end
