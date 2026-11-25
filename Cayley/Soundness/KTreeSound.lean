module

public import Cayley.Soundness.KDomSound

@[expose] public section

/-!
# Soundness of the kernel tree walk

`checkTree hok b t = true`, together with coverage of the holes of `t`, covers the box `b`: no point
of `b` is a reduced Rupert pose.
-/

namespace Cayley.Pack

open Cayley.Checker Noperthedron

/-- The invariants of the boxes produced by the walk. -/
structure Inv (b : Box) : Prop where
  chart : b.chart < 5
  face : b.face < 6
  lenc : b.c.length = 5
  lenh : b.h.length = 5
  hpos : ∀ i : Fin 5, 0 ≤ b.h.getD i 0
  mag : ∀ i : Fin 5, |b.c.getD i 0| + |b.h.getD i 0| ≤ 2 * 2 ^ b.K

/-- No point of the box is a reduced Rupert pose. -/
def Covered (b : Box) : Prop :=
  ∀ X ∈ b.pts, PtOK b.chart b.face X → ¬ Bad b.chart b.face X

/-! ## Splitting -/

theorem getD_set_eq (l : List ℤ) (d : ℕ) (x : ℤ) (hd : d < l.length) : (l.set d x).getD d 0 = x := by
  simp [List.getD_eq_getElem?_getD, hd]

theorem getD_set_ne (l : List ℤ) (d i : ℕ) (x : ℤ) (h : i ≠ d) : (l.set d x).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

theorem getD_map2 (l : List ℤ) (i : ℕ) : (l.map (2 * ·)).getD i 0 = 2 * l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem split_fst (b : Box) (d : ℕ) : (b.split d).1.chart = b.chart ∧ (b.split d).1.face = b.face := by
  unfold Box.split; dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩
theorem split_snd (b : Box) (d : ℕ) : (b.split d).2.chart = b.chart ∧ (b.split d).2.face = b.face := by
  unfold Box.split; dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩

theorem split_inv (b : Box) (hb : Inv b) (d : ℕ) (hd : d < 5) :
    Inv (b.split d).1 ∧ Inv (b.split d).2 := by
  have h0 := hb.hpos ⟨d, hd⟩
  have m0 := hb.mag ⟨d, hd⟩
  simp only at h0 m0
  have hlc : d < b.c.length := by rw [hb.lenc]; exact hd
  have hlh : d < b.h.length := by rw [hb.lenh]; exact hd
  have hK : (2 : ℤ) * 2 ^ (b.K + 1) = 2 * (2 * 2 ^ b.K) := by ring
  unfold Box.split; dsimp only
  split_ifs with he
  · have hh : 0 ≤ b.h.getD d 0 / 2 := Int.ediv_nonneg h0 (by norm_num)
    have h2 : 2 * (b.h.getD d 0 / 2) = b.h.getD d 0 := by omega
    have a1 := abs_sub (b.c.getD d 0) (b.h.getD d 0 / 2)
    have a2 := abs_add_le (b.c.getD d 0) (b.h.getD d 0 / 2)
    rw [abs_of_nonneg hh] at a1 a2
    rw [abs_of_nonneg h0] at m0
    refine ⟨⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_, fun i => ?_⟩,
      ⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_, fun i => ?_⟩⟩ <;>
    by_cases hi : (i : ℕ) = d
    · rw [hi, getD_set_eq _ _ _ hlh]; exact hh
    · rw [getD_set_ne _ _ _ _ hi]; exact hb.hpos i
    · rw [hi, getD_set_eq _ _ _ hlh, getD_set_eq _ _ _ hlc, abs_of_nonneg hh]; linarith
    · rw [getD_set_ne _ _ _ _ hi, getD_set_ne _ _ _ _ hi]; exact hb.mag i
    · rw [hi, getD_set_eq _ _ _ hlh]; exact hh
    · rw [getD_set_ne _ _ _ _ hi]; exact hb.hpos i
    · rw [hi, getD_set_eq _ _ _ hlh, getD_set_eq _ _ _ hlc, abs_of_nonneg hh]; linarith
    · rw [getD_set_ne _ _ _ _ hi, getD_set_ne _ _ _ _ hi]; exact hb.mag i
  · have a1 := abs_sub (2 * b.c.getD d 0) (b.h.getD d 0)
    have a2 := abs_add_le (2 * b.c.getD d 0) (b.h.getD d 0)
    rw [abs_mul, abs_two] at a1 a2
    refine ⟨⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_, fun i => ?_⟩,
      ⟨hb.chart, hb.face, by simp [hb.lenc], by simp [hb.lenh], fun i => ?_, fun i => ?_⟩⟩ <;>
    by_cases hi : (i : ℕ) = d
    · rw [hi, getD_set_eq _ _ _ (by simp [hb.lenh]; exact hd)]; exact h0
    · rw [getD_set_ne _ _ _ _ hi, getD_map2]; have := hb.hpos i; omega
    · rw [hi, getD_set_eq _ _ _ (by simp [hb.lenc]; exact hd),
        getD_set_eq _ _ _ (by simp [hb.lenh]; exact hd), hK]; linarith
    · rw [getD_set_ne _ _ _ _ hi, getD_set_ne _ _ _ _ hi, getD_map2, getD_map2, abs_mul, abs_mul,
        abs_two, hK]; linarith [hb.mag i]
    · rw [hi, getD_set_eq _ _ _ (by simp [hb.lenh]; exact hd)]; exact h0
    · rw [getD_set_ne _ _ _ _ hi, getD_map2]; have := hb.hpos i; omega
    · rw [hi, getD_set_eq _ _ _ (by simp [hb.lenc]; exact hd),
        getD_set_eq _ _ _ (by simp [hb.lenh]; exact hd), hK]; linarith
    · rw [getD_set_ne _ _ _ _ hi, getD_set_ne _ _ _ _ hi, getD_map2, getD_map2, abs_mul, abs_mul,
        abs_two, hK]; linarith [hb.mag i]

/-- Every point of a box is a point of one of its two halves. -/
theorem split_cover (b : Box) (hb : Inv b) (d : ℕ) (hd : d < 5) {X : Fin 5 → ℝ}
    (hX : X ∈ b.pts) : X ∈ (b.split d).1.pts ∨ X ∈ (b.split d).2.pts := by
  set D : Fin 5 := ⟨d, hd⟩
  have hlc : d < b.c.length := by rw [hb.lenc]; exact hd
  have hlh : d < b.h.length := by rw [hb.lenh]; exact hd
  have hlc2 : d < (b.c.map (2 * ·)).length := by simp [hb.lenc]; exact hd
  have hlh2 : d < (b.h.map (2 * ·)).length := by simp [hb.lenh]; exact hd
  have hD : |2 ^ b.K * X D - (b.c.getD d 0 : ℝ)| ≤ (b.h.getD d 0 : ℝ) := hX D
  rw [abs_le] at hD
  -- membership in a half: the coordinates other than `d`, and coordinate `d`
  have key : ∀ b' : Box,
      (∀ i : Fin 5, (i : ℕ) ≠ d → |2 ^ b'.K * X i - (b'.c.getD i 0 : ℝ)| ≤ (b'.h.getD i 0 : ℝ)) →
      |2 ^ b'.K * X D - (b'.c.getD d 0 : ℝ)| ≤ (b'.h.getD d 0 : ℝ) → X ∈ b'.pts := by
    intro b' h1 h2 i
    by_cases hi : (i : ℕ) = d
    · obtain rfl : i = D := Fin.ext hi
      exact h2
    · exact h1 i hi
  by_cases hneg : 2 ^ b.K * X D ≤ (b.c.getD d 0 : ℝ)
  all_goals
    unfold Box.split; dsimp only
    split_ifs with he
    · have h2 : ((b.h.getD d 0 / 2 : ℤ) : ℝ) * 2 = b.h.getD d 0 := by
        have : b.h.getD d 0 % 2 = 0 := by have := hb.hpos D; simp only [D] at this; omega
        exact_mod_cast Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero this)
      first
        | left
          refine key _ (fun i hi => ?_) ?_
          · simp only [getD_set_ne _ _ _ _ hi]; exact hX i
          · simp only [getD_set_eq _ _ _ hlc, getD_set_eq _ _ _ hlh]
            push_cast; rw [abs_le]; constructor <;> linarith
        | right
          refine key _ (fun i hi => ?_) ?_
          · simp only [getD_set_ne _ _ _ _ hi]; exact hX i
          · simp only [getD_set_eq _ _ _ hlc, getD_set_eq _ _ _ hlh]
            push_cast; rw [abs_le]; constructor <;> linarith
    · first
        | left
          refine key _ (fun i hi => ?_) ?_
          · simp only [getD_set_ne _ _ _ _ hi, getD_map2]
            have := abs_le.1 (hX i)
            push_cast; rw [pow_succ, abs_le]; constructor <;> linarith
          · simp only [getD_set_eq _ _ _ hlc2, getD_set_eq _ _ _ hlh2]
            push_cast; rw [pow_succ, abs_le]; constructor <;> linarith
        | right
          refine key _ (fun i hi => ?_) ?_
          · simp only [getD_set_ne _ _ _ _ hi, getD_map2]
            have := abs_le.1 (hX i)
            push_cast; rw [pow_succ, abs_le]; constructor <;> linarith
          · simp only [getD_set_eq _ _ _ hlc2, getD_set_eq _ _ _ hlh2]
            push_cast; rw [pow_succ, abs_le]; constructor <;> linarith

theorem split_big (b : Box) (hb : Inv b) (d : ℕ) (hd : 5 ≤ d) :
    (b.split d).1 = b ∧ (b.split d).2 = b := by
  have hh : b.h.getD d 0 = 0 := by
    simp [List.getD_eq_getElem?_getD, hb.lenh, hd]
  have hc : ∀ x : ℤ, b.c.set d x = b.c := fun x => List.set_eq_of_length_le (by rw [hb.lenc]; exact hd)
  have hh' : ∀ x : ℤ, b.h.set d x = b.h := fun x => List.set_eq_of_length_le (by rw [hb.lenh]; exact hd)
  unfold Box.split; dsimp only
  rw [hh]
  simp [hc, hh']

/-- A hole-free check has no holes. -/
theorem holes_nil (b : Box) (tr : Tree) (h : checkTree false b tr = true) : holes b tr = [] := by
  induction tr generalizing b with
  | split d l r ihl ihr =>
    simp only [checkTree, Bool.and_eq_true] at h
    simp only [holes, ihl _ h.1, ihr _ h.2, List.append_nil]
  | hole => simp [checkTree] at h
  | dom _ => rfl
  | gap _ _ _ => rfl

/-- **The tree walk.** A bad point of a checked box lies in one of its holes. -/
theorem walk (hok : Bool) (tr : Tree) : ∀ b, Inv b → checkTree hok b tr = true →
    ∀ X ∈ b.pts, PtOK b.chart b.face X → Bad b.chart b.face X →
    ∃ hb ∈ holes b tr, Inv hb ∧ hb.chart = b.chart ∧ hb.face = b.face ∧ X ∈ hb.pts := by
  induction tr with
  | hole => intro b hb _ X hX _ _; exact ⟨b, by simp [holes], hb, rfl, rfl, hX⟩
  | dom code =>
    intro b hb h X hX hpt hbad
    obtain ⟨t, ht, rfl⟩ := b.exists_kpt hX
    exact absurd hbad.1 (pDomOK_sound b hb.chart hb.face hb.hpos h ht hpt)
  | gap s w0 w1 =>
    intro b hb h X hX hpt hbad
    obtain ⟨t, ht, rfl⟩ := b.exists_kpt hX
    exact absurd hbad.2 (pGapOK_sound b hb.chart hb.face hb.lenc hb.lenh hb.mag h ht hpt)
  | split d l r ihl ihr =>
    intro b hb h X hX hpt hbad
    simp only [checkTree, Bool.and_eq_true] at h
    obtain ⟨c1, f1⟩ := split_fst b d
    obtain ⟨c2, f2⟩ := split_snd b d
    have hin : Inv (b.split d).1 ∧ Inv (b.split d).2 ∧
        (X ∈ (b.split d).1.pts ∨ X ∈ (b.split d).2.pts) := by
      rcases Nat.lt_or_ge d 5 with hd | hd
      · exact ⟨(split_inv b hb d hd).1, (split_inv b hb d hd).2, split_cover b hb d hd hX⟩
      · obtain ⟨e1, e2⟩ := split_big b hb d hd
        rw [e1, e2]; exact ⟨hb, hb, Or.inl hX⟩
    obtain ⟨i1, i2, hX1 | hX2⟩ := hin
    · obtain ⟨x, hx, hi, hc, hf, hm⟩ := ihl _ i1 h.1 X hX1 (by rw [c1, f1]; exact hpt)
        (by rw [c1, f1]; exact hbad)
      exact ⟨x, by simp [holes, hx], hi, hc.trans c1, hf.trans f1, hm⟩
    · obtain ⟨x, hx, hi, hc, hf, hm⟩ := ihr _ i2 h.2 X hX2 (by rw [c2, f2]; exact hpt)
        (by rw [c2, f2]; exact hbad)
      exact ⟨x, by simp [holes, hx], hi, hc.trans c2, hf.trans f2, hm⟩

/-- A hole-free checked box is covered. -/
theorem covered_of_check (b : Box) (hb : Inv b) (tr : Tree) (h : checkTree false b tr = true) :
    Covered b := by
  intro X hX hpt hbad
  obtain ⟨x, hx, -⟩ := walk false tr b hb h X hX hpt hbad
  rw [holes_nil b tr h] at hx
  simp at hx

end Cayley.Pack

end
