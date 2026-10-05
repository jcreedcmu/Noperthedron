module

public import Noperthedron.PentagonalHexecontahedron.NPoly

@[expose] public section

/-!
# Witness polynomials of the DH cap certificates

A chart of a cap certificate (nopert229 `capcert.cc`) is a polynomial map
s ↦ (u(s), w(s)) from a box in ℝ⁵ to views u and Cayley vectors w. For a
witness (vertex v_k, direction c) and a vertex v_j the witness polynomial is

  P_j = (N(w) v_k − D(w) v_j) · (u × c),
  N(w) v = (1 − |w|²) v + 2 (w·v) w + 2 w × v,  D(w) = 1 + |w|²,

built here with `NPoly` operations (`witnessPoly`), and evaluating it gives
the real expression (`eval_witnessPoly`). N(w)/D(w) is the Cayley rotation
(`Noperthedron.cayleyMatrix`), so P_j ≥ 0 says (R v_k)·d ≥ v_j·d.
-/

namespace Noperthedron.PentagonalHexecontahedron

/-- Polynomial vectors in the 5 chart variables. -/
abbrev PVec := Fin 3 → NPoly 5

/-- Exact vectors. -/
abbrev KVec := Fin 3 → IcoQ

namespace PVec

open NPoly

noncomputable def eval (p : PVec) (s : Fin 5 → ℝ) : Fin 3 → ℝ := fun i => NPoly.eval 5 (p i) s

def const (v : KVec) : PVec := fun i => NPoly.const 5 (v i)
def add (p q : PVec) : PVec := fun i => NPoly.add 5 (p i) (q i)
def sub (p q : PVec) : PVec := fun i => NPoly.sub 5 (p i) (q i)
def smul (a : NPoly 5) (p : PVec) : PVec := fun i => NPoly.mul 5 a (p i)
def dot (p q : PVec) : NPoly 5 :=
  NPoly.add 5 (NPoly.mul 5 (p 0) (q 0)) (NPoly.add 5 (NPoly.mul 5 (p 1) (q 1)) (NPoly.mul 5 (p 2) (q 2)))
def cross (p q : PVec) : PVec :=
  ![NPoly.sub 5 (NPoly.mul 5 (p 1) (q 2)) (NPoly.mul 5 (p 2) (q 1)),
    NPoly.sub 5 (NPoly.mul 5 (p 2) (q 0)) (NPoly.mul 5 (p 0) (q 2)),
    NPoly.sub 5 (NPoly.mul 5 (p 0) (q 1)) (NPoly.mul 5 (p 1) (q 0))]

/-- Real 3-vector helpers (on `Fin 3 → ℝ`). -/
def rdot (a b : Fin 3 → ℝ) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
def rcross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

noncomputable def kval (v : KVec) : Fin 3 → ℝ := fun i => (v i).val

theorem eval_const (v : KVec) (s : Fin 5 → ℝ) : (const v).eval s = kval v := by
  funext i; simp [eval, const, kval, NPoly.eval_const]

theorem eval_add (p q : PVec) (s : Fin 5 → ℝ) : (add p q).eval s = p.eval s + q.eval s := by
  funext i; simp [eval, add, NPoly.eval_add]

theorem eval_sub (p q : PVec) (s : Fin 5 → ℝ) : (sub p q).eval s = p.eval s - q.eval s := by
  funext i; simp [eval, sub, NPoly.eval_sub]

theorem eval_smul (a : NPoly 5) (p : PVec) (s : Fin 5 → ℝ) :
    (smul a p).eval s = NPoly.eval 5 a s • p.eval s := by
  funext i; simp [eval, smul, NPoly.eval_mul]

theorem eval_dot (p q : PVec) (s : Fin 5 → ℝ) : NPoly.eval 5 (dot p q) s = rdot (p.eval s) (q.eval s) := by
  simp [dot, rdot, eval, NPoly.eval_add, NPoly.eval_mul]
  ring

theorem eval_cross (p q : PVec) (s : Fin 5 → ℝ) : (cross p q).eval s = rcross (p.eval s) (q.eval s) := by
  funext i
  fin_cases i <;> simp [cross, rcross, eval, NPoly.eval_sub, NPoly.eval_mul]

end PVec

open PVec

theorem icoOne_val : IcoQ.one.val = 1 := by simp [IcoQ.val, IcoQ.one]

def npOne : NPoly 5 := NPoly.const 5 IcoQ.one
def npTwo : NPoly 5 := NPoly.const 5 (IcoQ.ofRat 2)

/-- N(w) v = (1 − |w|²) v + 2 (w·v) w + 2 w × v. -/
def cayleyNum (w : PVec) (v : KVec) : PVec :=
  let cv := PVec.const v
  PVec.add (PVec.smul (NPoly.sub 5 npOne (PVec.dot w w)) cv)
    (PVec.add (PVec.smul (NPoly.mul 5 npTwo (PVec.dot w cv)) w) (PVec.smul npTwo (PVec.cross w cv)))

/-- D(w) = 1 + |w|². -/
def cayleyDen (w : PVec) : NPoly 5 := NPoly.add 5 npOne (PVec.dot w w)

/-- The witness polynomials share N(w) v_k · d and D(w); per vertex j only v_j · d changes. -/
structure WitnessParts where
  nkd : NPoly 5
  den : NPoly 5
  d : PVec

def witnessParts (u w : PVec) (vk c : KVec) : WitnessParts :=
  let d := PVec.cross u (PVec.const c)
  { nkd := PVec.dot (cayleyNum w vk) d, den := cayleyDen w, d := d }

/-- P_j = N(w) v_k · d − D(w) (v_j · d). -/
def witnessPoly (parts : WitnessParts) (vj : KVec) : NPoly 5 :=
  NPoly.sub 5 parts.nkd (NPoly.mul 5 parts.den (PVec.dot (PVec.const vj) parts.d))

/-- The real numerator of the Cayley rotation. -/
def rcayleyNum (w v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (1 - rdot w w) • v + (2 * rdot w v) • w + (2 : ℝ) • rcross w v

theorem eval_cayleyNum (w : PVec) (v : KVec) (s : Fin 5 → ℝ) :
    (cayleyNum w v).eval s = rcayleyNum (w.eval s) (kval v) := by
  simp only [cayleyNum, rcayleyNum, PVec.eval_add, PVec.eval_smul, NPoly.eval_sub, NPoly.eval_mul,
    PVec.eval_dot, PVec.eval_cross, PVec.eval_const, npOne, npTwo, NPoly.eval_const, icoOne_val,
    IcoQ.val_ofRat]
  push_cast
  rw [add_assoc]

theorem eval_witnessPoly (u w : PVec) (vk c vj : KVec) (s : Fin 5 → ℝ) :
    NPoly.eval 5 (witnessPoly (witnessParts u w vk c) vj) s =
      rdot (rcayleyNum (w.eval s) (kval vk)) (rcross (u.eval s) (kval c)) -
        (1 + rdot (w.eval s) (w.eval s)) * rdot (kval vj) (rcross (u.eval s) (kval c)) := by
  simp only [witnessPoly, witnessParts, cayleyDen, NPoly.eval_sub, NPoly.eval_mul, NPoly.eval_add,
    PVec.eval_dot, PVec.eval_cross, PVec.eval_const, eval_cayleyNum, npOne, NPoly.eval_const,
    icoOne_val]

end Noperthedron.PentagonalHexecontahedron
