module

public import Cayley.Soundness.KDomSound

@[expose] public section

/-!
# Soundness of the kernel tree walk

`kCheck hok b t = true`, together with coverage of the holes of `t`, covers the box `b`: no point
of `b` is a reduced Rupert pose.
-/

namespace Cayley.Pack

open Cayley.K Noperthedron

/-- The invariants of the boxes produced by the walk. -/
structure Inv (b : KBox) : Prop where
  chart : b.chart < 5
  face : b.face < 6
  lenc : b.c.length = 5
  lenh : b.h.length = 5
  hpos : ∀ i : Fin 5, 0 ≤ b.h.getD i 0

/-- No point of the box is a reduced Rupert pose. -/
def Covered (b : KBox) : Prop :=
  ∀ t : Fin 5 → ℝ, (∀ i, |t i| ≤ 1) → PtOK b.chart b.face (kpt b t) → ¬ Bad b.chart b.face (kpt b t)


/-! ## Splitting -/

theorem getD_set_eq (l : List ℤ) (d : ℕ) (x : ℤ) (hd : d < l.length) : (l.set d x).getD d 0 = x := by
  simp [List.getD_eq_getElem?_getD, hd]

theorem getD_set_ne (l : List ℤ) (d i : ℕ) (x : ℤ) (h : i ≠ d) : (l.set d x).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

theorem getD_map2 (l : List ℤ) (i : ℕ) : (l.map (2 * ·)).getD i 0 = 2 * l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem split_fst (b : KBox) (d : ℕ) : (b.split d).1.chart = b.chart ∧ (b.split d).1.face = b.face := by
  unfold KBox.split; dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩
theorem split_snd (b : KBox) (d : ℕ) : (b.split d).2.chart = b.chart ∧ (b.split d).2.face = b.face := by
  unfold KBox.split; dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩

theorem split_inv (b : KBox) (hb : Inv b) (d : ℕ) (hd : d < 5) :
    Inv (b.split d).1 ∧ Inv (b.split d).2 := by
  have h0 := hb.hpos ⟨d, hd⟩
  simp only at h0
  unfold KBox.split; dsimp only
  split_ifs with he
  · have hh : 0 ≤ b.h.getD d 0 / 2 := Int.ediv_nonneg h0 (by norm_num)
    refine ⟨⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_⟩,
      ⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_⟩⟩ <;>
    · by_cases hi : (i : ℕ) = d
      · rw [hi, getD_set_eq _ _ _ (by rw [hb.lenh]; exact hd)]; exact hh
      · rw [getD_set_ne _ _ _ _ hi]; exact hb.hpos i
  · refine ⟨⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_⟩,
      ⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_⟩⟩ <;>
    · by_cases hi : (i : ℕ) = d
      · rw [hi, getD_set_eq _ _ _ (by simp [hb.lenh]; exact hd)]; exact h0
      · rw [getD_set_ne _ _ _ _ hi, getD_map2]; have := hb.hpos i; omega

/-- Every point of a box is a point of one of its two halves. -/
theorem split_cover (b : KBox) (hb : Inv b) (d : ℕ) (hd : d < 5) (t : Fin 5 → ℝ)
    (ht : ∀ i, |t i| ≤ 1) :
    (∃ t', (∀ i, |t' i| ≤ 1) ∧ kpt (b.split d).1 t' = kpt b t) ∨
      (∃ t', (∀ i, |t' i| ≤ 1) ∧ kpt (b.split d).2 t' = kpt b t) := by
  set D : Fin 5 := ⟨d, hd⟩
  have hD : (D : ℕ) = d := rfl
  have hlc : d < b.c.length := by rw [hb.lenc]; exact hd
  have hlh : d < b.h.length := by rw [hb.lenh]; exact hd
  have hlc2 : d < (b.c.map (2 * ·)).length := by simp [hb.lenc]; exact hd
  have hlh2 : d < (b.h.map (2 * ·)).length := by simp [hb.lenh]; exact hd
  have hU : (0 : ℝ) < 2 ^ b.K := by positivity
  have hunit : ∀ (s : ℝ), (∀ i, |t i| ≤ 1) → ∀ (v : ℝ), |v| ≤ 1 →
      ∀ i, |Function.update t D v i| ≤ 1 := by
    intro _ ht v hv i
    by_cases hi : i = D
    · subst hi; simpa using hv
    · simp [hi, ht i]
  by_cases hneg : t D ≤ 0
  · left
    refine ⟨Function.update t D (2 * t D + 1), hunit 0 ht _ ?_, ?_⟩
    · have := abs_le.1 (ht D); rw [abs_le]; constructor <;> linarith
    · funext i
      unfold KBox.split; dsimp only
      split_ifs with he
      · have h2 : ((b.h.getD d 0 / 2 : ℤ) : ℝ) * 2 = b.h.getD d 0 := by
          have : b.h.getD d 0 % 2 = 0 := by have := hb.hpos D; simp only [hD] at this; omega
          exact_mod_cast Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero this)
        by_cases hi : i = D
        · subst hi
          simp only [kpt, hD, getD_set_eq _ _ _ hlc, getD_set_eq _ _ _ hlh, Function.update_self]
          push_cast; congr 1; linear_combination (t D) * h2
        · have hi' : (i : ℕ) ≠ d := fun h => hi (Fin.ext h)
          simp only [kpt, getD_set_ne _ _ _ _ hi', Function.update_of_ne hi]
      · by_cases hi : i = D
        · subst hi
          simp only [kpt, hD, getD_set_eq _ _ _ hlc2, getD_set_eq _ _ _ hlh2, Function.update_self]
          push_cast; rw [pow_succ]; field_simp; ring
        · have hi' : (i : ℕ) ≠ d := fun h => hi (Fin.ext h)
          simp only [kpt, getD_set_ne _ _ _ _ hi', getD_map2, Function.update_of_ne hi]
          push_cast; rw [pow_succ]; field_simp
  · right
    push Not at hneg
    refine ⟨Function.update t D (2 * t D - 1), hunit 0 ht _ ?_, ?_⟩
    · have := abs_le.1 (ht D); rw [abs_le]; constructor <;> linarith
    · funext i
      unfold KBox.split; dsimp only
      split_ifs with he
      · have h2 : ((b.h.getD d 0 / 2 : ℤ) : ℝ) * 2 = b.h.getD d 0 := by
          have : b.h.getD d 0 % 2 = 0 := by have := hb.hpos D; simp only [hD] at this; omega
          exact_mod_cast Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero this)
        by_cases hi : i = D
        · subst hi
          simp only [kpt, hD, getD_set_eq _ _ _ hlc, getD_set_eq _ _ _ hlh, Function.update_self]
          push_cast; congr 1; linear_combination (t D) * h2
        · have hi' : (i : ℕ) ≠ d := fun h => hi (Fin.ext h)
          simp only [kpt, getD_set_ne _ _ _ _ hi', Function.update_of_ne hi]
      · by_cases hi : i = D
        · subst hi
          simp only [kpt, hD, getD_set_eq _ _ _ hlc2, getD_set_eq _ _ _ hlh2, Function.update_self]
          push_cast; rw [pow_succ]; field_simp; ring
        · have hi' : (i : ℕ) ≠ d := fun h => hi (Fin.ext h)
          simp only [kpt, getD_set_ne _ _ _ _ hi', getD_map2, Function.update_of_ne hi]
          push_cast; rw [pow_succ]; field_simp

theorem split_big (b : KBox) (hb : Inv b) (d : ℕ) (hd : 5 ≤ d) :
    (b.split d).1 = b ∧ (b.split d).2 = b := by
  have hh : b.h.getD d 0 = 0 := by
    simp [List.getD_eq_getElem?_getD, hb.lenh, hd]
  have hc : ∀ x : ℤ, b.c.set d x = b.c := fun x => List.set_eq_of_length_le (by rw [hb.lenc]; exact hd)
  have hh' : ∀ x : ℤ, b.h.set d x = b.h := fun x => List.set_eq_of_length_le (by rw [hb.lenh]; exact hd)
  unfold KBox.split; dsimp only
  rw [hh]
  simp [hc, hh']

/-- A hole-free check has no holes. -/
theorem holes_nil (b : KBox) (tr : KTree) (h : kCheck false b tr = true) : holes b tr = [] := by
  induction tr generalizing b with
  | split d l r ihl ihr =>
    simp only [kCheck, Bool.and_eq_true] at h
    simp only [holes, ihl _ h.1, ihr _ h.2, List.append_nil]
  | hole => simp [kCheck] at h
  | dom _ => rfl
  | gap _ _ _ => rfl

/-- **The tree walk.** A bad point of a checked box lies in one of its holes. -/
theorem walk (hok : Bool) (tr : KTree) : ∀ b, Inv b → kCheck hok b tr = true →
    ∀ t : Fin 5 → ℝ, (∀ i, |t i| ≤ 1) → PtOK b.chart b.face (kpt b t) →
    Bad b.chart b.face (kpt b t) →
    ∃ hb ∈ holes b tr, Inv hb ∧ hb.chart = b.chart ∧ hb.face = b.face ∧
      ∃ t', (∀ i, |t' i| ≤ 1) ∧ kpt hb t' = kpt b t := by
  induction tr with
  | hole => intro b hb _ t ht _ _; exact ⟨b, by simp [holes], hb, rfl, rfl, t, ht, rfl⟩
  | dom code =>
    intro b hb h t ht hpt hbad
    exact absurd hbad.1 (pDomOK_sound b hb.chart hb.face hb.hpos h ht hpt)
  | gap s w0 w1 =>
    intro b hb h t ht hpt hbad
    exact absurd hbad.2 (pGapOK_sound b hb.chart hb.face h ht hpt)
  | split d l r ihl ihr =>
    intro b hb h t ht hpt hbad
    simp only [kCheck, Bool.and_eq_true] at h
    obtain ⟨c1, f1⟩ := split_fst b d
    obtain ⟨c2, f2⟩ := split_snd b d
    have go : ∀ (b' : KBox) (sub : KTree), Inv b' → b'.chart = b.chart → b'.face = b.face →
        kCheck hok b' sub = true →
        (∀ b'', Inv b'' → kCheck hok b'' sub = true →
          ∀ t : Fin 5 → ℝ, (∀ i, |t i| ≤ 1) → PtOK b''.chart b''.face (kpt b'' t) →
          Bad b''.chart b''.face (kpt b'' t) →
          ∃ hb ∈ holes b'' sub, Inv hb ∧ hb.chart = b''.chart ∧ hb.face = b''.face ∧
            ∃ t', (∀ i, |t' i| ≤ 1) ∧ kpt hb t' = kpt b'' t) →
        ∀ t', (∀ i, |t' i| ≤ 1) → kpt b' t' = kpt b t →
        ∃ hb ∈ holes b' sub, Inv hb ∧ hb.chart = b.chart ∧ hb.face = b.face ∧
          ∃ t'', (∀ i, |t'' i| ≤ 1) ∧ kpt hb t'' = kpt b t := by
      intro b' sub hi hc hf hk ih t' ht' he
      rw [← hc, ← hf, ← he] at hpt hbad
      obtain ⟨hb', hm, hi', hc', hf', t'', ht'', he'⟩ := ih b' hi hk t' ht' hpt hbad
      exact ⟨hb', hm, hi', hc'.trans hc, hf'.trans hf, t'', ht'', he'.trans he⟩
    rcases Nat.lt_or_ge d 5 with hd | hd
    · obtain ⟨i1, i2⟩ := split_inv b hb d hd
      rcases split_cover b hb d hd t ht with ⟨t', ht', he⟩ | ⟨t', ht', he⟩
      · obtain ⟨x, hx, rest⟩ := go _ l i1 c1 f1 h.1 ihl t' ht' he
        exact ⟨x, by simp [holes, hx], rest⟩
      · obtain ⟨x, hx, rest⟩ := go _ r i2 c2 f2 h.2 ihr t' ht' he
        exact ⟨x, by simp [holes, hx], rest⟩
    · obtain ⟨e1, -⟩ := split_big b hb d hd
      have i1 : Inv (b.split d).1 := by rw [e1]; exact hb
      obtain ⟨x, hx, rest⟩ := go _ l i1 c1 f1 h.1 ihl t ht (by rw [e1])
      exact ⟨x, by simp [holes, hx], rest⟩

/-- A hole-free checked box is covered. -/
theorem covered_of_check (b : KBox) (hb : Inv b) (tr : KTree) (h : kCheck false b tr = true) :
    Covered b := by
  intro t ht hpt hbad
  obtain ⟨x, hx, -⟩ := walk false tr b hb h t ht hpt hbad
  rw [holes_nil b tr h] at hx
  simp at hx

end Cayley.Pack

end
