module

public import Cayley.Checker.Leaf

@[expose] public section

/-!
# Kernel tree walk

Boxes are `Box`es (integers over `2^K`); a split halves one radius, doubling the common
scale first when that radius is odd. `.hole` leaves mark subtrees that are checked by separate
theorems (see `holes`).
-/

namespace Cayley.Checker

inductive Tree where
  | split (d : Nat) (l r : Tree)
  | dom (code : Nat)
  | gap (s : Nat) (w0 w1 : Int)
  | hole

/-- Halve the radius in direction `d`. -/
def Box.split (b : Box) (d : Nat) : Box × Box :=
  let hd := b.h.getD d 0
  let cd := b.c.getD d 0
  if hd.toNat % 2 = 0 then
    let h' := hd / 2
    ({ b with c := b.c.set d (cd - h'), h := b.h.set d h' },
     { b with c := b.c.set d (cd + h'), h := b.h.set d h' })
  else
    let c2 := b.c.map (2 * ·)
    let h2 := b.h.map (2 * ·)
    ({ b with K := b.K + 1, c := c2.set d (2 * cd - hd), h := h2.set d hd },
     { b with K := b.K + 1, c := c2.set d (2 * cd + hd), h := h2.set d hd })

/-- The 15 root boxes (scale `2^2`): `u ∈ [0,1]`, `v ∈ [0,1/2]`, `r ∈ [-1,1]³` (charts 1–3),
`(c, ρ) ∈ [-1,1]² × [0,1]` (chart 0, faces 0–5), `(c, ρ) ∈ [-1,1]² × [0,2]` (chart 4). -/
def rootBox (i : Nat) : Box :=
  if i < 3 then ⟨i + 1, 0, 2, [2, 1, 0, 0, 0], [2, 1, 4, 4, 4]⟩
  else if i < 9 then ⟨0, i - 3, 2, [2, 1, 0, 0, 2], [2, 1, 4, 4, 2]⟩
  else ⟨4, i - 9, 2, [2, 1, 0, 0, 4], [2, 1, 4, 4, 4]⟩

/-- Check every leaf; `.hole` leaves pass exactly when `hok` (holes are then covered by
separate theorems, see `holes`). -/
def checkTree (hok : Bool) (b : Box) : Tree → Bool
  | .split d l r => checkTree hok (b.split d).1 l && checkTree hok (b.split d).2 r
  | .dom code => pDomOK b code
  | .gap s w0 w1 => pGapOK b s w0 w1
  | .hole => hok

/-- The boxes of the holes, left to right. -/
def holes (b : Box) : Tree → List Box
  | .split d l r => holes (b.split d).1 l ++ holes (b.split d).2 r
  | .hole => [b]
  | _ => []

/-- Every (box, subtree) pair checks, with no holes. -/
def AllOK : List (Box × Tree) → Prop
  | [] => True
  | (b, t) :: l => checkTree false b t = true ∧ AllOK l

end Cayley.Checker

end
