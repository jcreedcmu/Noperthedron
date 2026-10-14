module

public import Cayley.Soundness.Pack

@[expose] public section

/-!
# Polynomial expressions

`PE` is a tiny syntax for integer polynomials in five variables. `PE.ev` evaluates it in any
commutative ring; `PE.mv` is the polynomial itself. The syntactic degree `PE.deg` bounds every
exponent of `PE.mv`, and `PE.nrm` bounds the sum of the absolute values of its coefficients.
-/

namespace Cayley.Pack

open MvPolynomial

inductive PE where
  | c (z : ℤ)
  | x (i : Fin 5)
  | add (a b : PE)
  | sub (a b : PE)
  | mul (a b : PE)

namespace PE

/-- Evaluation in a commutative ring. -/
def ev {R : Type*} [CommRing R] (v : Fin 5 → R) : PE → R
  | c z => z
  | x i => v i
  | add a b => ev v a + ev v b
  | sub a b => ev v a - ev v b
  | mul a b => ev v a * ev v b

/-- The polynomial. -/
noncomputable def mv (e : PE) : MvPolynomial (Fin 5) ℤ := e.ev X

/-- Syntactic degree in variable `i`. -/
def deg (i : Fin 5) : PE → ℕ
  | c _ => 0
  | x j => if j = i then 1 else 0
  | add a b => max (deg i a) (deg i b)
  | sub a b => max (deg i a) (deg i b)
  | mul a b => deg i a + deg i b

/-- A bound on the sum of absolute values of the coefficients. -/
def nrm : PE → ℕ
  | c z => z.natAbs
  | x _ => 1
  | add a b => nrm a + nrm b
  | sub a b => nrm a + nrm b
  | mul a b => nrm a * nrm b

theorem mv_c (z : ℤ) : (c z).mv = C z := by simp [mv, ev]
theorem mv_x (i : Fin 5) : (x i).mv = X i := rfl
theorem mv_add (a b : PE) : (add a b).mv = a.mv + b.mv := rfl
theorem mv_sub (a b : PE) : (sub a b).mv = a.mv - b.mv := rfl
theorem mv_mul (a b : PE) : (mul a b).mv = a.mv * b.mv := rfl

/-- Evaluation is evaluation of the polynomial. -/
theorem ev_eq_eval₂ {R : Type*} [CommRing R] (v : Fin 5 → R) (e : PE) :
    e.ev v = eval₂Hom (Int.castRingHom R) v e.mv := by
  induction e with
  | c z => rw [mv_c, eval₂Hom_C]; simp [ev]
  | x i => rw [mv_x, eval₂Hom_X']; rfl
  | add a b iha ihb => rw [mv_add, map_add, ← iha, ← ihb]; rfl
  | sub a b iha ihb => rw [mv_sub, map_sub, ← iha, ← ihb]; rfl
  | mul a b iha ihb => rw [mv_mul, map_mul, ← iha, ← ihb]; rfl

theorem support_deg (e : PE) : ∀ m ∈ e.mv.support, ∀ i, m i ≤ e.deg i := by
  induction e with
  | c z =>
    intro m hm i
    classical
    rw [mv_c, support_C] at hm
    split_ifs at hm
    · simp at hm
    · rw [Finset.mem_singleton] at hm; simp [hm]
  | x j =>
    intro m hm i
    rw [mv_x, support_X, Finset.mem_singleton] at hm
    subst hm
    by_cases h : j = i <;> simp [deg, h]
  | add a b iha ihb =>
    intro m hm i
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact le_trans (iha m h i) (le_max_left _ _)
    · exact le_trans (ihb m h i) (le_max_right _ _)
  | sub a b iha ihb =>
    intro m hm i
    rw [mv_sub, sub_eq_add_neg] at hm
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact le_trans (iha m h i) (le_max_left _ _)
    · rw [support_neg] at h
      exact le_trans (ihb m h i) (le_max_right _ _)
  | mul a b iha ihb =>
    intro m hm i
    obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hm)
    simp only [Finsupp.add_apply, deg]
    exact Nat.add_le_add (iha p hp i) (ihb q hq i)

/-! ## The `ℓ¹` norm of the coefficients -/

/-- `Σ |coeff|`. -/
noncomputable def l1 (p : MvPolynomial (Fin 5) ℤ) : ℤ := ∑ m ∈ p.support, |p.coeff m|

theorem l1_eq_of_subset {p : MvPolynomial (Fin 5) ℤ} {s : Finset (Fin 5 →₀ ℕ)}
    (h : p.support ⊆ s) : l1 p = ∑ m ∈ s, |p.coeff m| :=
  Finset.sum_subset h fun m _ hm => by simp [notMem_support_iff.1 hm]

theorem l1_add_le (p q : MvPolynomial (Fin 5) ℤ) : l1 (p + q) ≤ l1 p + l1 q := by
  have hs : (p + q).support ⊆ p.support ∪ q.support := support_add
  rw [l1_eq_of_subset hs, l1_eq_of_subset (Finset.subset_union_left (s₂ := q.support)),
    l1_eq_of_subset (Finset.subset_union_right (s₁ := p.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by
    have hc : (p + q).coeff m = p.coeff m + q.coeff m := by simp
    rw [hc]; exact abs_add_le _ _

theorem l1_neg (p : MvPolynomial (Fin 5) ℤ) : l1 (-p) = l1 p := by
  simp [l1, support_neg]

theorem l1_sub_le (p q : MvPolynomial (Fin 5) ℤ) : l1 (p - q) ≤ l1 p + l1 q := by
  rw [sub_eq_add_neg]; exact (l1_add_le _ _).trans (by rw [l1_neg])

theorem l1_monomial (a : Fin 5 →₀ ℕ) (z : ℤ) : l1 (monomial a z) = |z| := by
  by_cases hz : z = 0
  · simp [hz, l1]
  · simp [l1, support_monomial, hz, coeff_monomial]

theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 5) ℤ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (l1_add_le _ _).trans (by linarith)

theorem l1_mul_le (p q : MvPolynomial (Fin 5) ℤ) : l1 (p * q) ≤ l1 p * l1 q := by
  have hp : p = ∑ a ∈ p.support, monomial a (p.coeff a) := (support_sum_monomial_coeff p).symm
  have hq : q = ∑ b ∈ q.support, monomial b (q.coeff b) := (support_sum_monomial_coeff q).symm
  have hpq : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support, monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [hp, hq]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [hpq]
  refine (l1_sum_le _ _).trans ?_
  calc ∑ a ∈ p.support, l1 (∑ b ∈ q.support, monomial (a + b) (p.coeff a * q.coeff b))
      ≤ ∑ a ∈ p.support, ∑ b ∈ q.support, |p.coeff a * q.coeff b| := by
        refine Finset.sum_le_sum fun a _ => (l1_sum_le _ _).trans ?_
        simp only [l1_monomial, le_refl]
    _ = l1 p * l1 q := by
        rw [l1, l1, Finset.sum_mul_sum]
        simp only [abs_mul]

theorem l1_le_nrm (e : PE) : l1 e.mv ≤ e.nrm := by
  induction e with
  | c z => rw [mv_c, ← monomial_zero', l1_monomial]; simp [nrm]
  | x i =>
    rw [mv_x, X, l1_monomial]; simp [nrm]
  | add a b iha ihb =>
    rw [mv_add]; push_cast [nrm]; exact (l1_add_le _ _).trans (by linarith)
  | sub a b iha ihb =>
    rw [mv_sub]; push_cast [nrm]; exact (l1_sub_le _ _).trans (by linarith)
  | mul a b iha ihb =>
    rw [mv_mul]; push_cast [nrm]
    refine (l1_mul_le _ _).trans ?_
    have h1 : 0 ≤ l1 a.mv := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h2 : 0 ≤ l1 b.mv := Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact mul_le_mul iha ihb h2 (by positivity)

theorem abs_coeff_le_l1 (p : MvPolynomial (Fin 5) ℤ) (m : Fin 5 →₀ ℕ) : |p.coeff m| ≤ l1 p := by
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m => |p.coeff m|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

end PE

end Cayley.Pack

end
