module

public import Cayley.Soundness.PackPoly
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Slot layouts

A layout numbers the exponent vectors `m` with `mᵢ < rᵢ` by the mixed-radix index
`idx m = Σ mᵢ sᵢ < n`. A polynomial whose exponents fit is the sum over the `n` slots of its
coefficients at `dig j`, both at the Kronecker point `tᵢ = 2^(W sᵢ)` and anywhere else.
-/

namespace Cayley.Pack

open MvPolynomial

structure Layout where
  r : Fin 5 → ℕ
  s : Fin 5 → ℕ
  n : ℕ

namespace Layout

variable (L : Layout)

def idx (m : Fin 5 → ℕ) : ℕ := m 0 * L.s 0 + m 1 * L.s 1 + m 2 * L.s 2 + m 3 * L.s 3 + m 4 * L.s 4

def dig (j : ℕ) (i : Fin 5) : ℕ := j / L.s i % L.r i

/-- The exponent vector of slot `j`. -/
noncomputable def digF (j : ℕ) : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm (L.dig j)

/-- The mixed-radix facts, checked by `decide` for each concrete layout. -/
structure Good : Prop where
  idx_dig : ∀ j < L.n, L.idx (L.dig j) = j
  dig_idx : ∀ m : Fin 5 → ℕ, (∀ i, m i < L.r i) → L.idx m < L.n ∧ ∀ i, L.dig (L.idx m) i = m i

/-- Slot `j` is even when every exponent is even. -/
def evSlot (j : ℕ) : Bool := (List.finRange 5).all fun i => L.dig j i % 2 == 0

variable {L}

theorem sum_support_eq {R : Type*} [AddCommMonoid R] (hL : L.Good) (p : MvPolynomial (Fin 5) ℤ)
    (hbox : ∀ m ∈ p.support, ∀ i, m i < L.r i) (H : (Fin 5 →₀ ℕ) → ℤ → R)
    (H0 : ∀ m, H m 0 = 0) :
    ∑ m ∈ p.support, H m (p.coeff m) =
      ∑ j ∈ Finset.range L.n, H (L.digF j) (p.coeff (L.digF j)) := by
  classical
  have hdi : ∀ m ∈ p.support, L.digF (L.idx m) = m := fun m hm => by
    ext i; exact (hL.dig_idx m (hbox m hm)).2 i
  have hsub : p.support.image (fun m : Fin 5 →₀ ℕ => L.idx m) ⊆ Finset.range L.n := by
    intro j hj
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (hL.dig_idx m (hbox m hm)).1
  have hzero : ∀ j ∈ Finset.range L.n, j ∉ p.support.image (fun m : Fin 5 →₀ ℕ => L.idx m) →
      H (L.digF j) (p.coeff (L.digF j)) = 0 := by
    intro j hj hni
    have : L.digF j ∉ p.support := fun hm =>
      hni (Finset.mem_image.2 ⟨_, hm, hL.idx_dig j (Finset.mem_range.1 hj)⟩)
    rw [notMem_support_iff.1 this, H0]
  have hinj : Set.InjOn (fun m : Fin 5 →₀ ℕ => L.idx m) p.support := by
    intro a ha b hb hab
    rw [← hdi a ha, ← hdi b hb]; exact congrArg _ hab
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun m hm => by rw [hdi m hm]

/-- Slot coefficients of a polynomial expression. -/
noncomputable def cf (L : Layout) (e : PE) (j : ℕ) : ℤ := e.mv.coeff (L.digF j)

/-- Exponents fit the layout. -/
def Fits (L : Layout) (e : PE) : Prop := ∀ i, e.deg i < L.r i

theorem fits_box {e : PE} (h : Fits L e) : ∀ m ∈ e.mv.support, ∀ i, m i < L.r i :=
  fun m hm i => lt_of_le_of_lt (PE.support_deg e m hm i) (h i)

theorem ev_eq_sum {R : Type*} [CommRing R] (hL : L.Good) {e : PE} (h : Fits L e)
    (v : Fin 5 → R) :
    e.ev v = ∑ j ∈ Finset.range L.n, (L.cf e j : R) * ∏ i, v i ^ L.dig j i := by
  rw [PE.ev_eq_eval₂, coe_eval₂Hom, eval₂_eq']
  exact sum_support_eq hL e.mv (fits_box h) (fun m z => (Int.castRingHom R z) * ∏ i, v i ^ m i)
    (fun m => by simp)

/-- At the Kronecker point. -/
theorem ev_kron (hL : L.Good) {e : PE} (h : Fits L e) (W : ℕ) :
    e.ev (fun i => (2 : ℤ) ^ (W * L.s i)) = ∑ j ∈ Finset.range L.n, L.cf e j * 2 ^ (W * j) := by
  rw [ev_eq_sum hL h]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  simp only [← pow_mul]
  rw [Fin.prod_univ_five, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  have hj' := hL.idx_dig j (Finset.mem_range.1 hj)
  calc _ = W * L.idx (L.dig j) := by simp only [idx]; ring
    _ = W * j := by rw [hj']

theorem abs_cf_le {e : PE} (j : ℕ) : |L.cf e j| ≤ e.nrm :=
  (PE.abs_coeff_le_l1 _ _).trans (PE.l1_le_nrm e)

theorem sum_abs_cf_le (hL : L.Good) {e : PE} (h : Fits L e) :
    ∑ j ∈ Finset.range L.n, |L.cf e j| ≤ e.nrm := by
  refine le_trans (le_of_eq ?_) (PE.l1_le_nrm e)
  exact (sum_support_eq hL e.mv (fits_box h) (fun _ z => |z|) (fun _ => abs_zero)).symm

end Layout

end Cayley.Pack

end
