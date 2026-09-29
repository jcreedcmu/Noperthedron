import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
import Noperthedron.Nopert229.TestConeLemma

open scoped BigOperators RealInnerProductSpace

namespace Noperthedron.Nopert229

/-- Adaptive 2D quadtree certifying cap coverage on the affine plane H = {x : inner x u0 = c_cone}. -/
inductive PlaneCoverTree where
  | outside : PlaneCoverTree
  | covered (axis_idx : Nat) : PlaneCoverTree
  | splitS (mid : ℚ) (left right : PlaneCoverTree) : PlaneCoverTree
  | splitT (mid : ℚ) (left right : PlaneCoverTree) : PlaneCoverTree
deriving DecidableEq, Repr

def dotQ (u v : Fin 3 → ℚ) : ℚ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def normSqQ (u : Fin 3 → ℚ) : ℚ :=
  dotQ u u

def basisE1 (u0 : Fin 3 → ℚ) : Fin 3 → ℚ :=
  if u0 0 ≠ 0 ∨ u0 1 ≠ 0 then
    ![ -u0 1, u0 0, 0 ]
  else
    ![ 0, -u0 2, u0 1 ]

def basisE2 (u0 e1 : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![
    u0 1 * e1 2 - u0 2 * e1 1,
    u0 2 * e1 0 - u0 0 * e1 2,
    u0 0 * e1 1 - u0 1 * e1 0
  ]

def basisP0 (u0 : Fin 3 → ℚ) (c_cone : ℚ) : Fin 3 → ℚ :=
  let u0_sq := normSqQ u0
  (c_cone / u0_sq) • u0

def checkCorner (u0 e1 e2 : Fin 3 → ℚ) (c_cone c_core : ℚ) (w : Fin 3 → ℚ) (s t : ℚ) : Bool :=
  let p0 := basisP0 u0 c_cone
  let V := p0 + s • e1 + t • e2
  let dot_V_w := dotQ V w
  let norm_sq_V := normSqQ V
  decide (0 ≤ dot_V_w) && decide (c_core^2 * norm_sq_V ≤ dot_V_w^2)

def checkCover (u0 e1 e2 : Fin 3 → ℚ) (D1 D2 norm_sq_p0 : ℚ) (c_cone c_core : ℚ)
    (flock : List (Fin 3 → ℚ)) (tree : PlaneCoverTree) (s0 s1 t0 t1 : ℚ) : Bool :=
  match tree with
  | .outside =>
      let s_min := if 0 ≤ s0 then s0 else if s1 ≤ 0 then -s1 else 0
      let t_min := if 0 ≤ t0 then t0 else if t1 ≤ 0 then -t1 else 0
      decide (1 < norm_sq_p0 + s_min^2 * D1 + t_min^2 * D2)
  | .covered axis_idx =>
      match flock[axis_idx]? with
      | none => false
      | some w =>
          checkCorner u0 e1 e2 c_cone c_core w s0 t0 &&
          checkCorner u0 e1 e2 c_cone c_core w s1 t0 &&
          checkCorner u0 e1 e2 c_cone c_core w s0 t1 &&
          checkCorner u0 e1 e2 c_cone c_core w s1 t1
  | .splitS mid left right =>
      decide (s0 ≤ mid) && decide (mid ≤ s1) &&
      checkCover u0 e1 e2 D1 D2 norm_sq_p0 c_cone c_core flock left s0 mid t0 t1 &&
      checkCover u0 e1 e2 D1 D2 norm_sq_p0 c_cone c_core flock right mid s1 t0 t1
  | .splitT mid left right =>
      decide (t0 ≤ mid) && decide (mid ≤ t1) &&
      checkCover u0 e1 e2 D1 D2 norm_sq_p0 c_cone c_core flock left s0 s1 t0 mid &&
      checkCover u0 e1 e2 D1 D2 norm_sq_p0 c_cone c_core flock right s0 s1 mid t1

def checkFullTree (u0 : Fin 3 → ℚ) (c_cone c_core : ℚ) (flock : List (Fin 3 → ℚ))
    (S_max T_max : ℚ) (tree : PlaneCoverTree) : Bool :=
  let e1 := basisE1 u0
  let e2 := basisE2 u0 e1
  let D1 := normSqQ e1
  let D2 := normSqQ e2
  let p0 := basisP0 u0 c_cone
  let norm_sq_p0 := normSqQ p0
  decide (1 ≤ S_max^2 * D1) &&
  decide (1 ≤ T_max^2 * D2) &&
  decide (0 ≤ S_max) &&
  decide (0 ≤ T_max) &&
  checkCover u0 e1 e2 D1 D2 norm_sq_p0 c_cone c_core flock tree (-S_max) S_max (-T_max) T_max

end Noperthedron.Nopert229
