module

@[expose] public section

/-!
# Unnormalized dyadic numbers

`⟨m, e⟩ : QI` is `m / 2^e`. Operations never normalize: addition aligns exponents by a
multiplication with `2^d` (computed with `Nat.pow`, which the kernel evaluates with GMP), and
comparison cross-multiplies. Every operation is a handful of `Int`/`Nat` primitives, which keeps
`decide +kernel` evaluation cheap (core `Dyadic` normalizes with a well-founded loop).
-/

namespace Cayley

/-- The dyadic number `m / 2^e`. -/
structure QI where
  m : Int
  e : Nat
deriving Inhabited

namespace QI

/-- `2^k` as an integer. -/
@[inline] def pow2 (k : Nat) : Int := ((2 ^ k : Nat) : Int)

protected def add (a b : QI) : QI :=
  if a.e ≤ b.e then ⟨a.m * pow2 (b.e - a.e) + b.m, b.e⟩
  else ⟨a.m + b.m * pow2 (a.e - b.e), a.e⟩

protected def mul (a b : QI) : QI := ⟨a.m * b.m, a.e + b.e⟩

protected def neg (a : QI) : QI := ⟨-a.m, a.e⟩

protected def sub (a b : QI) : QI := QI.add a (QI.neg b)

instance : Add QI := ⟨QI.add⟩
instance : Mul QI := ⟨QI.mul⟩
instance : Neg QI := ⟨QI.neg⟩
instance : Sub QI := ⟨QI.sub⟩
instance (n : Nat) : OfNat QI n := ⟨⟨n, 0⟩⟩
instance : IntCast QI := ⟨fun n => ⟨n, 0⟩⟩
instance : NatCast QI := ⟨fun n => ⟨n, 0⟩⟩

/-- `a ≤ b` by cross-multiplication. -/
protected def le (a b : QI) : Prop := a.m * pow2 b.e ≤ b.m * pow2 a.e
protected def lt (a b : QI) : Prop := a.m * pow2 b.e < b.m * pow2 a.e

instance : LE QI := ⟨QI.le⟩
instance : LT QI := ⟨QI.lt⟩
instance (a b : QI) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.m * pow2 b.e ≤ b.m * pow2 a.e))
instance (a b : QI) : Decidable (a < b) := inferInstanceAs (Decidable (a.m * pow2 b.e < b.m * pow2 a.e))

end QI

end Cayley

end
