import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.SimpleRing.Principal

import Noperthedron.PushLeft

open Real
open Complex

namespace Cyclotomic
noncomputable section

def ω (N : ℕ) : ℂ := exp (2 * π * I / N)

lemma ω_wrap (N : ℕ) [NeZero N] : ω N ^ N = 1 := by
  have : (N : ℂ) ≠ 0 := by aesop
  simp only [ω, ← Complex.exp_nat_mul];
  field_simp
  exact exp_two_pi_mul_I

def cyclic_sum (N : ℕ) := ∑ n : Fin N, (ω N)^(n : ℕ)

lemma cyclic_sum_mul_eq (N : ℕ) (hN : 1 ≤ N) : ω N * cyclic_sum N = cyclic_sum N := by
  simp only [cyclic_sum, Finset.mul_sum]
  conv => lhs; rhs; intro i; rw [mul_comm]; change ω N ^ ((i : ℕ) + 1)
  let M := N - 1
  have hM : M + 1 = N := Nat.sub_add_cancel hN
  repeat rw [← hM]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [ω_wrap, Fin.coe_castSucc, Fin.val_last, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Fin.val_succ]
  ring_nf

lemma cyclic_sum_mul_eq' (N : ℕ) (hN : 1 ≤ N) : (ω N - 1) * cyclic_sum N = 0 := by
  have hh (a b : ℂ) (h : a * b = b) : (a - 1) * b = 0 := by push_lefta h
  exact hh (ω N) (cyclic_sum N) (cyclic_sum_mul_eq N hN)

lemma primitive_root_not_one (N : ℕ) (hN : 1 < N) : ω N ≠ 1 := by
  have : (N : ℂ) ≠ 0 := by aesop
  intro h
  let ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  field_simp at hn
  rw [show (1 : ℂ) = (↑(1 : ℤ) : ℂ) by push_cast; rfl] at hn
  rw [show (↑N : ℂ) * (↑n : ℂ) = (↑(N * n) : ℂ) by push_cast; rfl] at hn
  simp only [Int.cast_inj] at hn
  have z := Int.eq_one_or_neg_one_of_mul_eq_one hn.symm
  simp only [Nat.cast_eq_one, Int.reduceNeg, reduceCtorEq, or_false] at z
  linarith

lemma cyclic_sum_eq_zero (N : ℕ) (hN : 1 < N) : cyclic_sum N = 0 := by
  have : ω N - 1 ≠ 0 := fun k =>
    primitive_root_not_one N hN (by push_lefta k)
  have : NeZero N := { out := by intro a; subst a; simp_all only [not_neg] }
  cases (mul_eq_zero.mp) (cyclic_sum_mul_eq' N (le_of_lt hN)) <;> simp_all

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
