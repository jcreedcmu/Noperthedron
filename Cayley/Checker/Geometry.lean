module

@[expose] public section

/-!
# Exact data for the Cayley checker

Integer approximations of `2^80 cos(2πk/15)` and `2^80 sin(2πk/15)` (for the symmetry
rotations `Rz(2πk/15)`), the half-turn `τ` data, and the paired vertices of the blown-up
charts. Mathlib-free.
-/

namespace Cayley

/-- `2^80 cos(2πk/15)`, to within 1. -/
def cosTab : Array Int := #[
  1208925819614629174706176, 1104408691135802787572491, 808929266721616466411793,
  373578623199582567987662, -126367158128905632231740, -604462909807314587353088,
  -978041533006897155340750, -1182507889921199034399455, -1182507889921199034399455,
  -978041533006897155340750, -604462909807314587353088, -126367158128905632231740,
  373578623199582567987662, 808929266721616466411793, 1104408691135802787572491]

/-- `2^80 sin(2πk/15)`, to within 1. -/
def sinTab : Array Int := #[
  0, 491714429597714652495797, 898406967232629382321357,
  1149756778461952459611063, 1202303197482784322232552, 1046960471077192669696698,
  710588767885069669736755, 251349811229323077289706, -251349811229323077289706,
  -710588767885069669736755, -1046960471077192669696698, -1202303197482784322232552,
  -1149756778461952459611063, -898406967232629382321357, -491714429597714652495797]

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

end Cayley

end
