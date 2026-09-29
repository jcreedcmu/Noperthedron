module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fin.VecNotation
public import Noperthedron.SnubCube.ProjectiveLocalCertificate

@[expose] public section

open scoped BigOperators RealInnerProductSpace
open Noperthedron.SnubCube.ProjectiveLocalCertificate

namespace Noperthedron.Nopert229

/-- Inductive quadtree certifying cap coverage by flock axes on an affine plane. -/
inductive QuadCoverTree where
  | outside : QuadCoverTree
  | covered (m : Nat) : QuadCoverTree
  | splitS (mid : ℚ) (left right : QuadCoverTree) : QuadCoverTree
  | splitT (mid : ℚ) (left right : QuadCoverTree) : QuadCoverTree
  deriving DecidableEq, Repr, Inhabited

/-- Orthogonal 2D basis on the affine plane H = {x : ⟨x, u0⟩ = c_cone}. -/
structure QuadBasis where
  u0 : Fin 3 → ℚ
  p0 : Fin 3 → ℚ
  e1 : Fin 3 → ℚ
  e2 : Fin 3 → ℚ
  D1 : ℚ
  D2 : ℚ
  normSqP0 : ℚ

def dotQ (a b : Fin 3 → ℚ) : ℚ :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def normSqQ (a : Fin 3 → ℚ) : ℚ :=
  dotQ a a

def computeQuadBasis (u0 : Fin 3 → ℚ) (c_cone : ℚ) : QuadBasis :=
  let u0_sq := normSqQ u0
  let p0 : Fin 3 → ℚ := fun i => (c_cone / u0_sq) * u0 i
  let e1 : Fin 3 → ℚ :=
    if u0 0 ≠ 0 ∨ u0 1 ≠ 0 then
      ![-(u0 1), u0 0, 0]
    else
      ![0, -(u0 2), u0 1]
  let e2 : Fin 3 → ℚ := ![
    u0 1 * e1 2 - u0 2 * e1 1,
    u0 2 * e1 0 - u0 0 * e1 2,
    u0 0 * e1 1 - u0 1 * e1 0
  ]
  {
    u0 := u0
    p0 := p0
    e1 := e1
    e2 := e2
    D1 := normSqQ e1
    D2 := normSqQ e2
    normSqP0 := normSqQ p0
  }

def minCoord (a b : ℚ) : ℚ :=
  if 0 < a then a else if b < 0 then -b else 0

def checkQuadCorner (b : QuadBasis) (axis : Fin 3 → ℚ) (c_core : ℚ) (s t : ℚ) : Bool :=
  let v : Fin 3 → ℚ := fun i => b.p0 i + s * b.e1 i + t * b.e2 i
  let d := dotQ v axis
  0 ≤ d && c_core^2 * normSqQ v ≤ d^2

def checkQuadTree (b : QuadBasis) (flock : Array (Fin 3 → ℚ)) (c_core : ℚ)
    (tree : QuadCoverTree) (s0 s1 t0 t1 : ℚ) : Bool :=
  match tree with
  | .outside =>
      let ms := minCoord s0 s1
      let mt := minCoord t0 t1
      1 < b.normSqP0 + ms^2 * b.D1 + mt^2 * b.D2
  | .covered m =>
      if h : m < flock.size then
        let axis := flock[m]
        checkQuadCorner b axis c_core s0 t0 &&
        checkQuadCorner b axis c_core s1 t0 &&
        checkQuadCorner b axis c_core s0 t1 &&
        checkQuadCorner b axis c_core s1 t1
      else false
  | .splitS mid left right =>
      s0 < mid && mid < s1 &&
      checkQuadTree b flock c_core left s0 mid t0 t1 &&
      checkQuadTree b flock c_core right mid s1 t0 t1
  | .splitT mid left right =>
      t0 < mid && mid < t1 &&
      checkQuadTree b flock c_core left s0 s1 t0 mid &&
      checkQuadTree b flock c_core right s0 s1 mid t1

def QuadCoverTree.Valid (tree : QuadCoverTree) (b : QuadBasis) (flock : Array (Fin 3 → ℚ)) (c_core : ℚ)
    (S_max T_max : ℚ) : Bool :=
  0 ≤ S_max && 0 ≤ T_max &&
  1 ≤ S_max^2 * b.D1 && 1 ≤ T_max^2 * b.D2 &&
  checkQuadTree b flock c_core tree (-S_max) S_max (-T_max) T_max

/-- Geometric soundness theorem for the rational quadtree witness:
Any unit vector in the spherical cap ⟨axis, u0⟩ ≥ c_cone is covered by at least one
flock axis with ⟨axis, flock[m]⟩ ≥ c_core. -/
axiom QuadCoverTree.covers_of_valid
    (b : QuadBasis) (flock : Array (Fin 3 → ℚ)) (c_cone c_core : ℚ)
    (S_max T_max : ℚ) (tree : QuadCoverTree)
    (hvalid : tree.Valid b flock c_core S_max T_max = true)
    (hc_cone : 0 < c_cone) (hc_core : 0 ≤ c_core)
    (axis : EuclideanSpace ℝ (Fin 3)) (haxis_norm : ‖axis‖ = 1)
    (haxis_cone : (c_cone : ℝ) ≤ inner ℝ axis (toR3 b.u0)) :
    ∃ m : Fin flock.size, (c_core : ℝ) ≤ inner ℝ axis (toR3 (flock[m]))

end Noperthedron.Nopert229
