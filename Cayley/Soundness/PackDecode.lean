module

public import Cayley.Soundness.PackLayout
public import Cayley.Checker.KPack

@[expose] public section

/-!
# Soundness of the packed lower bound

For a polynomial expression `e` that fits a layout and has `nrm e < 2^(PW-12)`, the checker's
mask computation `pLowerL` applied to `e` evaluated at the Kronecker point is a lower bound of
`e` on `[-1,1]⁵`; similarly for the fields of `pStatsL`.
-/

namespace Cayley.Pack

open Cayley.K

/-! ## Masks on packed numbers -/

variable {W : ℕ} {n : ℕ}

theorem land_mask {d m : ℕ → ℕ} (hd : ∀ j < n, d j < 2 ^ W) (hm : ∀ j < n, m j ≤ 1) (hW : 0 < W) :
    packN W d n &&& packN W (fun j => (2 ^ W - 1) * m j) n = packN W (fun j => m j * d j) n := by
  have hmask : ∀ j < n, (2 ^ W - 1) * m j < 2 ^ W := fun j hj => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hm j hj) with h | h <;> rw [h] <;> simp
  rw [packN_land hW hd hmask]
  refine packN_congr fun j hj => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hm j hj) with h | h <;> rw [h]
  · simp
  · simp only [mul_one, one_mul]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hd j hj)]

theorem packN_ind0 (hn : 0 < n) (a : ℕ) : packN W (fun j => if j = 0 then a else 0) n = a := by
  rw [packN_eq_sum, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_range.2 hn) h

/-! ## The decode -/

/-! The checker writes `Nat.land a b` etc.; these are the notations. -/
theorem nat_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem nat_shiftRight (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem nat_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem nat_add (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nat_sub (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem nat_mod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem pM_eq : pM = 2 ^ PW - 1 := by delta pM; rfl
theorem PW_pos : 0 < PW := by decide

/-- The offset `2^(PW-1)`. -/
def O : ℕ := 2 ^ (PW - 1)

theorem O_lt : O < 2 ^ PW := Nat.pow_lt_pow_right (by norm_num) (by decide)
theorem O_pos : 0 < O := Nat.two_pow_pos _

/-- Numbers of the form `2^(PW-1) + c` with `|c| < 2^(PW-1)`. -/
theorem digit_lt {c : ℤ} (hc : |c| < (O : ℤ)) : (c + O).toNat < 2 ^ PW := by
  have h : ((2 ^ PW : ℕ) : ℤ) = 2 * (O : ℤ) := by
    rw [O]; push_cast; rw [← pow_succ']; rfl
  have := (abs_lt.1 hc).2
  have h2 : (0 : ℤ) < O := by exact_mod_cast O_pos
  omega

/-- Offset digits. -/
def odig (c : ℕ → ℤ) (j : ℕ) : ℕ := (c j + O).toNat

theorem odig_lt {c : ℕ → ℤ} {n : ℕ} (hc : ∀ j < n, |c j| < O) : ∀ j < n, odig c j < 2 ^ PW :=
  fun j hj => digit_lt (hc j hj)

/-- The sign of an offset digit. -/
theorem odig_div {c : ℤ} (hc : |c| < O) :
    (c + O).toNat / O = if 0 ≤ c then 1 else 0 := by
  have hO : (0 : ℤ) < O := by exact_mod_cast O_pos
  have h1 := (abs_lt.1 hc).1
  have h2 := (abs_lt.1 hc).2
  split_ifs with h
  · apply Nat.div_eq_of_lt_le
    · omega
    · have : ((2 * O : ℕ) : ℤ) = 2 * (O : ℤ) := by push_cast; ring
      omega
  · apply Nat.div_eq_of_lt_le <;> omega

/-- `pParts` on offset digits gives the positive and negative parts. -/
theorem pParts_eq {n : ℕ} (c : ℕ → ℤ) (hc : ∀ j < n, |c j| < O) :
    pParts (packN PW (fun _ => 1) n) (packN PW (odig c) n) =
      (packN PW (fun j => (max (c j) 0).toNat) n, packN PW (fun j => (max (-c j) 0).toNat) n) := by
  have hd := odig_lt hc
  set σ : ℕ → ℕ := fun j => if 0 ≤ c j then 1 else 0 with hσdef
  have hσ1 : ∀ j < n, σ j ≤ 1 := fun j _ => by simp only [σ]; split_ifs <;> simp
  have hsig : (packN PW (odig c) n >>> (PW - 1)) &&& packN PW (fun _ => 1) n = packN PW σ n := by
    rw [packN_signs PW_pos hd]
    exact packN_congr fun j hj => odig_div (hc j hj)
  have hpm : pM * (packN PW (odig c) n >>> (PW - 1) &&& packN PW (fun _ => 1) n) =
      packN PW (fun j => (2 ^ PW - 1) * σ j) n := by
    rw [hsig, packN_mul_left, pM_eq]
  have hnm : pM * packN PW (fun _ => 1) n - packN PW (fun j => (2 ^ PW - 1) * σ j) n =
      packN PW (fun j => (2 ^ PW - 1) * (1 - σ j)) n := by
    rw [packN_mul_left, pM_eq, ← packN_sub]
    · exact packN_congr fun j _ => by rw [Nat.mul_sub, mul_one]
    · intro j hj; exact Nat.mul_le_mul_left _ (by simpa using hσ1 j hj)
  have hσ1' : ∀ j < n, 1 - σ j ≤ 1 := fun _ _ => Nat.sub_le _ _
  have hoff : 2 ^ (PW - 1) * packN PW (fun _ => 1) n = packN PW (fun _ => O) n := by
    rw [packN_mul_left]; simp [O]
  have hO : ∀ j < n, (fun _ => O) j < 2 ^ PW := fun _ _ => O_lt
  simp only [pParts, nat_land, nat_shiftRight, nat_mul, nat_sub, hpm, hnm, hoff,
    land_mask hd hσ1 PW_pos, land_mask hO hσ1 PW_pos, land_mask hd hσ1' PW_pos,
    land_mask hO hσ1' PW_pos]
  have key : ∀ j < n, σ j * O ≤ σ j * odig c j ∧ (1 - σ j) * odig c j ≤ (1 - σ j) * O := by
    intro j hj
    have := (abs_lt.1 (hc j hj))
    simp only [σ, odig]
    split_ifs with h <;> simp <;> omega
  rw [← packN_sub fun j hj => (key j hj).1, ← packN_sub fun j hj => (key j hj).2]
  refine Prod.ext (packN_congr fun j hj => ?_) (packN_congr fun j hj => ?_) <;>
    have := abs_lt.1 (hc j hj) <;>
    simp only [σ, odig, max_def] <;> split_ifs <;> omega

/-! ## Masks of a layout -/

/-- The Kronecker point of a layout. -/
def kron (L : Layout) (i : Fin 5) : ℤ := 2 ^ (PW * L.s i)

/-- Slot indicators. -/
def evI (L : Layout) (j : ℕ) : ℕ := if L.evSlot j then 1 else 0
def oddI (L : Layout) (j : ℕ) : ℕ := if L.evSlot j then 0 else 1
def nzI (j : ℕ) : ℕ := if j = 0 then 0 else 1

theorem mask_odd (L : Layout) :
    pM * (packN PW (fun _ => 1) L.n - packN PW (evI L) L.n) =
      packN PW (fun j => (2 ^ PW - 1) * oddI L j) L.n := by
  rw [← packN_sub fun j _ => by simp only [evI]; split_ifs <;> simp, packN_mul_left, pM_eq]
  exact packN_congr fun j _ => by simp only [evI, oddI]; split_ifs <;> simp

theorem mask_nz (L : Layout) (hn : 0 < L.n) :
    pM * packN PW (fun _ => 1) L.n - pM = packN PW (fun j => (2 ^ PW - 1) * nzI j) L.n := by
  have e1 := packN_ind0 (W := PW) hn pM
  calc pM * packN PW (fun _ => 1) L.n - pM
      = packN PW (fun _ => pM * 1) L.n - packN PW (fun j => if j = 0 then pM else 0) L.n := by
        rw [packN_mul_left, e1]
    _ = _ := by
        rw [← packN_sub fun j _ => by split_ifs <;> simp]
        exact packN_congr fun j _ => by simp only [nzI, pM_eq]; split_ifs <;> simp

theorem mask_evnz (L : Layout) (hn : 0 < L.n) (h0 : L.evSlot 0 = true) :
    pM * (packN PW (evI L) L.n - 1) = packN PW (fun j => (2 ^ PW - 1) * (evI L j * nzI j)) L.n := by
  have e1 := packN_ind0 (W := PW) hn 1
  have hle : ∀ j < L.n, (fun j => if j = 0 then 1 else 0) j ≤ evI L j := fun j _ => by
    by_cases hj : j = 0
    · subst hj; simp [evI, h0]
    · simp [hj]
  calc pM * (packN PW (evI L) L.n - 1)
      = pM * (packN PW (evI L) L.n - packN PW (fun j => if j = 0 then 1 else 0) L.n) := by rw [e1]
    _ = _ := by
        rw [← packN_sub hle, packN_mul_left, pM_eq]
        refine packN_congr fun j _ => ?_
        by_cases hj : j = 0
        · subst hj; simp [evI, nzI, h0]
        · simp [nzI, hj]

/-! ## The encoding -/

/-- The checker's `Nat` encoding of `e` at the Kronecker point is the packed offset digits. -/
theorem enc_eq {L : Layout} (hL : L.Good) {e : PE} (h : L.Fits e)
    (hc : ∀ j < L.n, |L.cf e j| < O) :
    Int.toNat (Int.add (e.ev (kron L)) ((2 ^ (PW - 1) * packN PW (fun _ => 1) L.n : ℕ) : ℤ)) =
      packN PW (odig (L.cf e)) L.n := by
  have hk : e.ev (kron L) = ∑ j ∈ Finset.range L.n, L.cf e j * 2 ^ (PW * j) := Layout.ev_kron hL h PW
  have hsum : e.ev (kron L) + ((2 ^ (PW - 1) * packN PW (fun _ => 1) L.n : ℕ) : ℤ) =
      ((packN PW (odig (L.cf e)) L.n : ℕ) : ℤ) := by
    rw [hk, packN_eq_sum, packN_eq_sum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := abs_lt.1 (hc j (Finset.mem_range.1 hj))
    have hO : ((2 : ℤ) ^ (PW - 1)) = (O : ℤ) := by simp [O]
    rw [odig, Int.toNat_of_nonneg (by omega), hO]
    ring
  rw [show Int.add (e.ev (kron L)) ((2 ^ (PW - 1) * packN PW (fun _ => 1) L.n : ℕ) : ℤ) =
    e.ev (kron L) + ((2 ^ (PW - 1) * packN PW (fun _ => 1) L.n : ℕ) : ℤ) from rfl, hsum,
    Int.toNat_natCast]

/-! ## The lower bound in closed form -/

/-- Positive and negative parts of the slot coefficients. -/
noncomputable def posC (L : Layout) (e : PE) (j : ℕ) : ℕ := (max (L.cf e j) 0).toNat
noncomputable def negC (L : Layout) (e : PE) (j : ℕ) : ℕ := (max (-L.cf e j) 0).toNat

theorem posC_add_negC (L : Layout) (e : PE) (j : ℕ) : ((posC L e j + negC L e j : ℕ) : ℤ) = |L.cf e j| := by
  rw [abs_eq_max_neg]; simp only [posC, negC]; push_cast; omega

theorem posC_lt {L : Layout} {e : PE} {j : ℕ} (hc : |L.cf e j| < O) : posC L e j < 2 ^ PW := by
  have := posC_add_negC L e j
  have := O_lt
  omega

theorem negC_lt {L : Layout} {e : PE} {j : ℕ} (hc : |L.cf e j| < O) : negC L e j < 2 ^ PW := by
  have := posC_add_negC L e j
  have := O_lt
  omega

theorem oddI_le (L : Layout) (j : ℕ) : oddI L j ≤ 1 := by simp only [oddI]; split_ifs <;> simp
theorem nzI_le (j : ℕ) : nzI j ≤ 1 := by simp only [nzI]; split_ifs <;> simp
theorem evI_le (L : Layout) (j : ℕ) : evI L j ≤ 1 := by simp only [evI]; split_ifs <;> simp

/-- The slack of the lower bound. -/
noncomputable def slackC (L : Layout) (e : PE) : ℕ :=
  ∑ j ∈ Finset.range L.n, (oddI L j * posC L e j + nzI j * negC L e j)

theorem slackC_le (L : Layout) (e : PE) :
    (slackC L e : ℤ) ≤ ∑ j ∈ Finset.range L.n, |L.cf e j| := by
  rw [slackC]; push_cast
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← posC_add_negC]; push_cast
  have h1 := oddI_le L j; have h2 := nzI_le j
  have : (oddI L j : ℤ) * posC L e j ≤ posC L e j := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;> rw [h] <;> simp
  have : (nzI j : ℤ) * negC L e j ≤ negC L e j := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h | h <;> rw [h] <;> simp
  linarith

theorem pLowerL_eq {L : Layout} (hL : L.Good) {e : PE} (h : L.Fits e) (hn : 0 < L.n)
    (hc : ∀ j < L.n, |L.cf e j| < O) (hS : ∑ j ∈ Finset.range L.n, |L.cf e j| < (pM : ℤ)) :
    pLowerL (packN PW (fun _ => 1) L.n) (packN PW (evI L) L.n) (e.ev (kron L)) =
      L.cf e 0 - slackC L e := by
  have hsl : slackC L e < 2 ^ PW - 1 := by
    have := slackC_le L e; rw [pM_eq] at hS
    have : (2 : ℤ) ^ PW - 1 = ((2 ^ PW - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    omega
  have hpos := fun j hj => posC_lt (hc j hj)
  have hneg := fun j hj => negC_lt (hc j hj)
  have hP := pParts_eq (n := L.n) (L.cf e) hc
  simp only [posC, negC] at hpos hneg
  unfold pLowerL
  simp only [nat_mul]
  simp only [enc_eq hL h hc, hP, nat_land, nat_sub, nat_add, nat_mod]
  rw [mask_odd L, mask_nz L hn, land_mask hpos (fun j _ => oddI_le L j) PW_pos,
    land_mask hneg (fun j _ => nzI_le j) PW_pos, ← packN_add, pM_eq,
    packN_mod (by simpa [slackC, posC, negC] using hsl), packN_land_low PW_pos (odig_lt hc) hn]
  have h0 := abs_lt.1 (hc 0 hn)
  have hO : (2 : ℤ) ^ (PW - 1) = O := by simp [O]
  rw [Int.subNatNat_eq_coe, odig, Int.toNat_of_nonneg (by omega)]
  simp only [slackC, posC, negC]
  push_cast
  rw [hO]
  ring

/-! ## Real-valued bounds -/

theorem mono_abs_le {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) (k : Fin 5 → ℕ) :
    |∏ i, t i ^ k i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ht i)

theorem mono_nonneg (t : Fin 5 → ℝ) {k : Fin 5 → ℕ} (hk : ∀ i, Even (k i)) :
    0 ≤ ∏ i, t i ^ k i :=
  Finset.prod_nonneg fun i _ => (hk i).pow_nonneg _

theorem evSlot_even {L : Layout} {j : ℕ} (h : L.evSlot j = true) (i : Fin 5) : Even (L.dig j i) := by
  simp only [Layout.evSlot, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  exact Nat.even_iff.2 (h i)

theorem evSlot_zero (L : Layout) : L.evSlot 0 = true := by
  simp [Layout.evSlot, Layout.dig]

theorem dig_zero (L : Layout) (i : Fin 5) : L.dig 0 i = 0 := by simp [Layout.dig]

/-- One slot's contribution. -/
theorem slot_le {L : Layout} {e : PE} {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) (j : ℕ) :
    (if j = 0 then (L.cf e j : ℝ) else 0) - ((oddI L j * posC L e j + nzI j * negC L e j : ℕ) : ℝ) ≤
      (L.cf e j : ℝ) * ∏ i, t i ^ L.dig j i := by
  have hpn : ((posC L e j : ℕ) : ℝ) + negC L e j = |(L.cf e j : ℝ)| := by
    exact_mod_cast posC_add_negC L e j
  have hneg : ((negC L e j : ℕ) : ℝ) = max (-(L.cf e j : ℝ)) 0 := by
    have h1 : (((max (-L.cf e j) 0).toNat : ℕ) : ℤ) = max (-L.cf e j) 0 :=
      Int.toNat_of_nonneg (le_max_right _ _)
    have h2 : (((max (-L.cf e j) 0).toNat : ℕ) : ℝ) = ((max (-L.cf e j) 0 : ℤ) : ℝ) := by
      exact_mod_cast h1
    simp only [negC]; rw [h2]; push_cast; rfl
  set c : ℝ := (L.cf e j : ℝ)
  set μ := ∏ i, t i ^ L.dig j i
  have hμ := mono_abs_le ht (L.dig j)
  have hcμ : -|c| ≤ c * μ := by
    have := abs_mul c μ
    have : |c| * |μ| ≤ |c| := mul_le_of_le_one_right (abs_nonneg _) hμ
    linarith [neg_abs_le (c * μ)]
  by_cases hj : j = 0
  · subst hj
    have h1 : μ = 1 := by simp [μ, dig_zero]
    simp [oddI, nzI, evSlot_zero, h1]
  · simp only [hj, ↓reduceIte, nzI, one_mul, zero_sub]
    by_cases he : L.evSlot j = true
    · simp only [oddI, he, ↓reduceIte, zero_mul, zero_add]
      rw [hneg]
      have hμ0 : 0 ≤ μ := mono_nonneg t (evSlot_even he)
      have hμ1 : μ ≤ 1 := le_trans (le_abs_self _) hμ
      rcases le_total 0 c with hc | hc
      · rw [max_eq_right (by linarith)]; simp; positivity
      · rw [max_eq_left (by linarith)]; nlinarith
    · simp only [oddI, he, Bool.false_eq_true, ↓reduceIte, one_mul]
      push_cast; linarith

theorem lower_le_ev {L : Layout} (hL : L.Good) {e : PE} (h : L.Fits e) (hn : 0 < L.n)
    {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) :
    ((L.cf e 0 - slackC L e : ℤ) : ℝ) ≤ e.ev t := by
  rw [Layout.ev_eq_sum hL h t, slackC]
  have hz : ((L.cf e 0 : ℤ) : ℝ) =
      ∑ j ∈ Finset.range L.n, (if j = 0 then (L.cf e j : ℝ) else 0) := by
    rw [Finset.sum_ite_eq' (Finset.range L.n) 0 (fun j => (L.cf e j : ℝ))]
    simp [Finset.mem_range.2 hn]
  push_cast
  rw [hz, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun j _ => by exact_mod_cast slot_le ht j

/-! ## The statistics -/

/-- The absolute deviation bound. -/
noncomputable def absC (L : Layout) (e : PE) : ℕ :=
  ∑ j ∈ Finset.range L.n, nzI j * (posC L e j + negC L e j)

theorem abs_ev_sub_le {L : Layout} (hL : L.Good) {e : PE} (h : L.Fits e) (hn : 0 < L.n)
    {t : Fin 5 → ℝ} (ht : ∀ i, |t i| ≤ 1) :
    |e.ev t - (L.cf e 0 : ℝ)| ≤ absC L e := by
  rw [Layout.ev_eq_sum hL h t, absC]
  have hz : ((L.cf e 0 : ℤ) : ℝ) =
      ∑ j ∈ Finset.range L.n, (if j = 0 then (L.cf e j : ℝ) else 0) := by
    rw [Finset.sum_ite_eq' (Finset.range L.n) 0 (fun j => (L.cf e j : ℝ))]
    simp [Finset.mem_range.2 hn]
  rw [hz, ← Finset.sum_sub_distrib]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hpn : ((posC L e j : ℕ) : ℝ) + negC L e j = |(L.cf e j : ℝ)| := by
    exact_mod_cast posC_add_negC L e j
  by_cases hj : j = 0
  · subst hj; simp [dig_zero, nzI]
  · simp only [hj, ↓reduceIte, sub_zero, nzI, Nat.cast_one, one_mul, hpn, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (mono_abs_le ht _)

/-- The statistics of the checker, in closed form. -/
theorem pStatsL_eq {L : Layout} (hL : L.Good) {e : PE} (h : L.Fits e) (hn : 0 < L.n)
    (hc : ∀ j < L.n, |L.cf e j| < O) (hS : ∑ j ∈ Finset.range L.n, |L.cf e j| < (pM : ℤ)) :
    let st := pStatsL (packN PW (fun _ => 1) L.n) (packN PW (evI L) L.n) (e.ev (kron L))
    st.c0 = L.cf e 0 ∧ st.slack = slackC L e ∧ st.abs = absC L e := by
  intro st
  have hpos := fun j hj => posC_lt (hc j hj)
  have hneg := fun j hj => negC_lt (hc j hj)
  have hab : ∀ j < L.n, posC L e j + negC L e j < 2 ^ PW := fun j hj => by
    have h1 := posC_add_negC L e j; have h2 := hc j hj; have := O_lt; omega
  have hP := pParts_eq (n := L.n) (L.cf e) hc
  have hsum : ∑ j ∈ Finset.range L.n, (posC L e j + negC L e j) < 2 ^ PW - 1 := by
    have : ((∑ j ∈ Finset.range L.n, (posC L e j + negC L e j) : ℕ) : ℤ) =
        ∑ j ∈ Finset.range L.n, |L.cf e j| := by
      push_cast; exact Finset.sum_congr rfl fun j _ => by exact_mod_cast posC_add_negC L e j
    rw [pM_eq] at hS
    have h2 : ((2 ^ PW - 1 : ℕ) : ℤ) = 2 ^ PW - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    omega
  have hle : ∀ (f : ℕ → ℕ), (∀ j, f j ≤ posC L e j + negC L e j) →
      ∑ j ∈ Finset.range L.n, f j < 2 ^ PW - 1 :=
    fun f hf => lt_of_le_of_lt (Finset.sum_le_sum fun j _ => hf j) hsum
  simp only [posC, negC] at hpos hneg hab
  refine ⟨?_, ?_, ?_⟩
  · simp only [st, pStatsL, nat_mul]
    simp only [enc_eq hL h hc, nat_land]
    rw [pM_eq, packN_land_low PW_pos (odig_lt hc) hn, Int.subNatNat_eq_coe, odig,
      Int.toNat_of_nonneg (by have := abs_lt.1 (hc 0 hn); omega)]
    simp [O]
  · simp only [st, pStatsL, nat_mul]
    simp only [enc_eq hL h hc, hP, nat_land, nat_sub, nat_add, nat_mod]
    rw [← packN_add, mask_odd L, mask_evnz L hn (evSlot_zero L),
      land_mask hab (fun j _ => oddI_le L j) PW_pos]
    rw [land_mask hneg (fun j _ => by simp only [evI, nzI]; split_ifs <;> simp) PW_pos, ← packN_add, pM_eq,
      packN_mod (hle _ fun j => ?_)]
    · simp only [slackC, posC, negC]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = 0
      · subst hj; simp [oddI, evI, nzI, evSlot_zero]
      · by_cases he : L.evSlot j = true <;> simp [oddI, evI, nzI, he, hj]
    · simp only [posC, negC, oddI, evI, nzI]
      split_ifs <;> omega
  · simp only [st, pStatsL, nat_mul]
    simp only [enc_eq hL h hc, hP, nat_land, nat_sub, nat_add, nat_mod]
    rw [← packN_add, mask_nz L hn, land_mask hab (fun j _ => nzI_le j) PW_pos, pM_eq,
      packN_mod (hle _ fun j => by simp only [nzI]; split_ifs <;> simp [posC, negC])]
    rfl

end Cayley.Pack

end
