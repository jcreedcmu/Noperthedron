import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.SimpleRing.Principal

import Noperthedron.PushLeft

open Real
open Complex

namespace Cyclotomic
noncomputable section

def ω (N : ℕ) : ℂ := exp (2 * π * I / N)

def z := ω 15

def q3 : 1 + z ^ 5 + z ^ 10 = 0 := by
  let z' := ω 3
  have h0 : IsPrimitiveRoot z' 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have qq := IsPrimitiveRoot.geom_sum_eq_zero h0 (by norm_num)
  have hpow : z' = z ^ 5 := by
    simp [z', z, ω, ← Complex.exp_nat_mul]
    ring_nf
  simp only [Finset.sum_range, Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod,
    Fin.val_succ, Finset.univ_unique, Fin.val_eq_zero, Finset.sum_const,
    Finset.card_singleton, hpow, ← pow_mul] at qq
  ring_nf at qq ⊢
  exact qq

def q5 : 1 + z ^ 3 + z ^ 6 + z ^ 9 + z ^ 12 = 0 := by
  let z' := ω 5
  have h0 : IsPrimitiveRoot z' 5 := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have qq := IsPrimitiveRoot.geom_sum_eq_zero h0 (by norm_num)
  have hpow : z' = z ^ 3 := by
    simp [z', z, ω, ← Complex.exp_nat_mul]
    ring_nf
  simp only [Finset.sum_range, Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod,
    Fin.val_succ, Finset.univ_unique, Fin.val_eq_zero, Finset.sum_const,
    Finset.card_singleton, hpow, ← pow_mul] at qq
  ring_nf at qq ⊢
  exact qq

def q3a : z ^ 13 = - z ^ 8 - z ^ 3 := by
  have h1 := congrArg (z ^ 3 * ·) q3
  push_lefta h1

def q3b : z ^ 10 = - z ^ 5 - 1 := by
  have h1 := q3
  push_lefta h1

def q5' : z ^ 8 = -1 + z - z ^ 3 + z ^ 4 -z ^ 5 + z ^ 7 := by
  have h' := congrArg (z * ·) q5
  ring_nf at h'
  rw [q3a, q3b] at h'
  have h'' := congrArg (-1 * ·) h'
  push_lefta h''
