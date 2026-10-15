module

public import Cayley.Soundness.KTreeSound
public import Cayley.Soundness.Reduction

@[expose] public section

/-!
# The main soundness theorem of the kernel checker

If each of the 15 root boxes carries a checked skeleton whose holes are checked hole-free
subtrees, then the Noperthedron is not Rupert.
-/

namespace Cayley.Pack

open Cayley.K Noperthedron Real
open scoped Matrix

theorem face_ax0 (r : Fin 3 → ℝ) (R : ℝ) (hR : ∀ i, |r i| ≤ R)
    (hmax : ∀ i, |r i| ≤ |r 0|) (hpos : 0 < |r 0|) :
    ∃ face < 6, ∃ ρ s0 s1 : ℝ, 0 ≤ ρ ∧ ρ ≤ R ∧ |s0| ≤ 1 ∧ |s1| ≤ 1 ∧
      ρ • faceR face s0 s1 = r := by
  have hq : ∀ i, |r i / abs (r 0)| ≤ 1 := fun i => by
    rw [abs_div, abs_abs, div_le_one hpos]; exact hmax i
  have hra : r 0 ≠ 0 := abs_pos.mp hpos
  rcases le_or_gt 0 (r 0) with hs | hs
  · refine ⟨0, by norm_num, |r 0|, r 1 / |r 0|, r 2 / |r 0|, hpos.le, hR 0, hq 1, hq 2, ?_⟩
    rw [abs_of_nonneg hs]
    ext i; fin_cases i <;> simp [faceR] <;> field_simp
  · refine ⟨1, by norm_num, |r 0|, r 1 / |r 0|, r 2 / |r 0|, hpos.le, hR 0, hq 1, hq 2, ?_⟩
    rw [abs_of_neg hs]
    ext i; fin_cases i <;> simp [faceR] <;> field_simp

theorem face_ax1 (r : Fin 3 → ℝ) (R : ℝ) (hR : ∀ i, |r i| ≤ R)
    (hmax : ∀ i, |r i| ≤ |r 1|) (hpos : 0 < |r 1|) :
    ∃ face < 6, ∃ ρ s0 s1 : ℝ, 0 ≤ ρ ∧ ρ ≤ R ∧ |s0| ≤ 1 ∧ |s1| ≤ 1 ∧
      ρ • faceR face s0 s1 = r := by
  have hq : ∀ i, |r i / abs (r 1)| ≤ 1 := fun i => by
    rw [abs_div, abs_abs, div_le_one hpos]; exact hmax i
  have hra : r 1 ≠ 0 := abs_pos.mp hpos
  rcases le_or_gt 0 (r 1) with hs | hs
  · refine ⟨2, by norm_num, |r 1|, r 2 / |r 1|, r 0 / |r 1|, hpos.le, hR 1, hq 2, hq 0, ?_⟩
    rw [abs_of_nonneg hs]
    ext i; fin_cases i <;> simp [faceR] <;> field_simp
  · refine ⟨3, by norm_num, |r 1|, r 2 / |r 1|, r 0 / |r 1|, hpos.le, hR 1, hq 2, hq 0, ?_⟩
    rw [abs_of_neg hs]
    ext i; fin_cases i <;> simp [faceR] <;> field_simp

theorem face_ax2 (r : Fin 3 → ℝ) (R : ℝ) (hR : ∀ i, |r i| ≤ R)
    (hmax : ∀ i, |r i| ≤ |r 2|) (hpos : 0 < |r 2|) :
    ∃ face < 6, ∃ ρ s0 s1 : ℝ, 0 ≤ ρ ∧ ρ ≤ R ∧ |s0| ≤ 1 ∧ |s1| ≤ 1 ∧
      ρ • faceR face s0 s1 = r := by
  have hq : ∀ i, |r i / abs (r 2)| ≤ 1 := fun i => by
    rw [abs_div, abs_abs, div_le_one hpos]; exact hmax i
  have hra : r 2 ≠ 0 := abs_pos.mp hpos
  rcases le_or_gt 0 (r 2) with hs | hs
  · refine ⟨4, by norm_num, |r 2|, r 0 / |r 2|, r 1 / |r 2|, hpos.le, hR 2, hq 0, hq 1, ?_⟩
    rw [abs_of_nonneg hs]
    ext i; fin_cases i <;> simp [faceR] <;> field_simp
  · refine ⟨5, by norm_num, |r 2|, r 0 / |r 2|, r 1 / |r 2|, hpos.le, hR 2, hq 0, hq 1, ?_⟩
    rw [abs_of_neg hs]
    ext i; fin_cases i <;> simp [faceR] <;> field_simp

/-- Every vector with `|rᵢ| ≤ R` is `ρ c` for `c` on a face of the unit cube. -/
theorem exists_face (r : Fin 3 → ℝ) (R : ℝ) (hR : ∀ i, |r i| ≤ R) :
    ∃ face < 6, ∃ ρ s0 s1 : ℝ, 0 ≤ ρ ∧ ρ ≤ R ∧ |s0| ≤ 1 ∧ |s1| ≤ 1 ∧
      ρ • faceR face s0 s1 = r := by
  by_cases hz : r = 0
  · refine ⟨0, by norm_num, 0, 0, 0, le_rfl, le_trans (abs_nonneg _) (hR 0), by simp, by simp, ?_⟩
    rw [hz, zero_smul]
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun i => |r i|) Finset.univ_nonempty
  have hmax : ∀ i, |r i| ≤ |r a| := fun i => ha i (Finset.mem_univ _)
  have hpos : 0 < |r a| := by
    by_contra hle
    push Not at hle
    apply hz
    funext i
    have : |r i| = 0 := le_antisymm (le_trans (hmax i) hle) (abs_nonneg _)
    simpa using this
  fin_cases a
  · exact face_ax0 r R hR hmax hpos
  · exact face_ax1 r R hR hmax hpos
  · exact face_ax2 r R hR hmax hpos

/-! ## The root boxes -/

theorem rootK_plain (i : ℕ) (hi : i < 3) :
    (rootK i).chart = i + 1 ∧ ∀ t : Fin 5 → ℝ, kpt (rootK i) t =
      ![1 / 2 + 1 / 2 * t 0, 1 / 4 + 1 / 4 * t 1, t 2, t 3, t 4] := by
  refine ⟨by simp [rootK, hi], fun t => ?_⟩
  funext k; fin_cases k <;> simp [rootK, hi, kpt] <;> ring

theorem rootK_blow0 (f : ℕ) (hf : f < 6) :
    (rootK (3 + f)).chart = 0 ∧ (rootK (3 + f)).face = f ∧
      ∀ t : Fin 5 → ℝ, kpt (rootK (3 + f)) t =
        ![1 / 2 + 1 / 2 * t 0, 1 / 4 + 1 / 4 * t 1, t 2, t 3, 1 / 2 + 1 / 2 * t 4] := by
  have h1 : ¬ 3 + f < 3 := by omega
  have h2 : 3 + f < 9 := by omega
  refine ⟨by simp [rootK, h1, h2], by simp [rootK, h1, h2], fun t => ?_⟩
  funext k; fin_cases k <;> simp [rootK, h1, h2, kpt] <;> ring

theorem rootK_blow4 (f : ℕ) (hf : f < 6) :
    (rootK (9 + f)).chart = 4 ∧ (rootK (9 + f)).face = f ∧
      ∀ t : Fin 5 → ℝ, kpt (rootK (9 + f)) t =
        ![1 / 2 + 1 / 2 * t 0, 1 / 4 + 1 / 4 * t 1, t 2, t 3, 1 + t 4] := by
  have h1 : ¬ 9 + f < 3 := by omega
  have h2 : ¬ 9 + f < 9 := by omega
  refine ⟨by simp [rootK, h1, h2], by simp [rootK, h1, h2], fun t => ?_⟩
  funext k; fin_cases k <;> simp [rootK, h1, h2, kpt] <;> ring

theorem rootK_inv (i : ℕ) (hi : i < 15) : Inv (rootK i) := by
  interval_cases i <;>
    exact ⟨by decide, by decide, rfl, rfl, fun k => by fin_cases k <;> decide⟩

/-! ## Coverage -/

theorem cover {u v : ℝ} {j : ℕ} {r : Fin 3 → ℝ} (hred : Reduced u v j r) :
    ∃ i < 15, ∃ t : Fin 5 → ℝ, (∀ k, |t k| ≤ 1) ∧ (rootK i).chart = j ∧
      kpt (rootK i) t 0 = u ∧ kpt (rootK i) t 1 = v ∧
      rOf (kblow j) (rootK i).face (kpt (rootK i) t) = r ∧
      PtOK (rootK i).chart (rootK i).face (kpt (rootK i) t) := by
  have hu1 : u ≤ 1 := by nlinarith [hred.disk, sq_nonneg v, hred.u_nonneg]
  have hv : v ≤ 1 / 2 := by linarith [hred.wedge]
  have hu0 := hred.u_nonneg
  have hv0 := hred.v_nonneg
  have hrb := hred.rb
  have hj := hred.j_lt
  have hU : |2 * u - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hV : |4 * v - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  by_cases hj04 : j = 0 ∨ j = 4
  · obtain ⟨f, hf, ρ, s0, s1, hρ0, hρR, hs0, hs1, hr⟩ := exists_face r _ hrb
    have hrr : ∀ (X : Fin 5 → ℝ), X = ![u, v, s0, s1, ρ] → rOf (kblow j) f X = r := by
      intro X hX
      rcases hj04 with rfl | rfl <;> simpa [hX, rOf, kblow] using hr
    rcases hj04 with rfl | rfl
    · obtain ⟨hc, hface, hpt⟩ := rootK_blow0 f hf
      simp only [show ((0 : ℕ) = 4) = False by decide, ite_false] at hρR
      set t : Fin 5 → ℝ := ![2 * u - 1, 4 * v - 1, s0, s1, 2 * ρ - 1]
      have hX : kpt (rootK (3 + f)) t = ![u, v, s0, s1, ρ] := by
        rw [hpt]; funext k; fin_cases k <;> simp [t] <;> ring
      refine ⟨3 + f, by omega, t, ?_, hc, by rw [hX]; rfl, by rw [hX]; rfl, ?_, ?_⟩
      · intro k; fin_cases k <;> simp [t, hU, hV, hs0, hs1]
        exact abs_le.2 ⟨by linarith, by linarith⟩
      · rw [hface]; exact hrr _ hX
      · rw [hc, hface, hX]
        refine ⟨by simpa using hred.disk, fun i => ?_, fun _ => ?_⟩
        · rw [hrr _ rfl]; have := hrb i; simp at this; linarith
        · simp; exact ⟨hρ0, by linarith, hs0, hs1⟩
    · obtain ⟨hc, hface, hpt⟩ := rootK_blow4 f hf
      simp only [ite_true] at hρR
      set t : Fin 5 → ℝ := ![2 * u - 1, 4 * v - 1, s0, s1, ρ - 1]
      have hX : kpt (rootK (9 + f)) t = ![u, v, s0, s1, ρ] := by
        rw [hpt]; funext k; fin_cases k <;> simp [t] <;> ring
      refine ⟨9 + f, by omega, t, ?_, hc, by rw [hX]; rfl, by rw [hX]; rfl, ?_, ?_⟩
      · intro k; fin_cases k <;> simp [t, hU, hV, hs0, hs1]
        exact abs_le.2 ⟨by linarith, by linarith⟩
      · rw [hface]; exact hrr _ hX
      · rw [hc, hface, hX]
        refine ⟨by simpa using hred.disk, fun i => ?_, fun _ => ?_⟩
        · rw [hrr _ rfl]; have := hrb i; simpa using this
        · simp; exact ⟨hρ0, hρR, hs0, hs1⟩
  · push Not at hj04
    have hj13 : j - 1 < 3 := by omega
    obtain ⟨hc, hpt⟩ := rootK_plain (j - 1) hj13
    have hkb : kblow j = false := by simp [kblow, hj04.1, hj04.2]
    have hr1 : ∀ i, |r i| ≤ 1 := fun i => by have := hrb i; simpa [hj04.2] using this
    set t : Fin 5 → ℝ := ![2 * u - 1, 4 * v - 1, r 0, r 1, r 2]
    have hX : kpt (rootK (j - 1)) t = ![u, v, r 0, r 1, r 2] := by
      rw [hpt]; funext k; fin_cases k <;> simp [t] <;> ring
    have hjc : (rootK (j - 1)).chart = j := by rw [hc]; omega
    have hrr : rOf (kblow j) (rootK (j - 1)).face ![u, v, r 0, r 1, r 2] = r := by
      rw [hkb]; funext k; fin_cases k <;> simp [rOf]
    refine ⟨j - 1, by omega, t, ?_, hjc, by rw [hX]; rfl, by rw [hX]; rfl, by rw [hX, hrr], ?_⟩
    · intro k; fin_cases k <;> simp [t, hU, hV, hr1]
    · rw [hjc, hX]
      refine ⟨by simpa using hred.disk, fun i => ?_, fun h => by simp [hkb] at h⟩
      rw [hrr]; linarith [hr1 i]

/-! ## Assembly -/

theorem AllOK_mem {P : List (KBox × KTree)} (h : AllOK P) :
    ∀ p ∈ P, kCheck false p.1 p.2 = true := by
  induction P with
  | nil => simp
  | cons q P ih =>
    obtain ⟨b, t⟩ := q
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact ih h.2 p hp

/-- A root skeleton whose holes are checked hole-free subtrees covers its box. -/
theorem root_covered (b : KBox) (hb : Inv b) (S : KTree) (P : List (KBox × KTree))
    (hs : kCheck true b S = true) (hh : holes b S = P.map Prod.fst) (ha : AllOK P) :
    Covered b := by
  intro t ht hpt hbad
  obtain ⟨x, hx, hix, hc, hf, t', ht', he⟩ := walk true S b hb hs t ht hpt hbad
  rw [hh, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  apply covered_of_check p.1 hix p.2 (AllOK_mem ha p hp) t' ht'
  · rw [hc, hf, he]; exact hpt
  · rw [hc, hf, he]; exact hbad

/-- The certificate facts for one root box. -/
def RootOK (i : ℕ) : Prop :=
  ∃ S : KTree, ∃ P : List (KBox × KTree),
    kCheck true (rootK i) S = true ∧ holes (rootK i) S = P.map Prod.fst ∧ AllOK P

/-- **Main soundness theorem.** Certificates for the 15 root boxes refute Rupertness. -/
theorem kernel_sound (h : ∀ i < 15, RootOK i) : ¬ IsRupert exactVerts := by
  intro hR
  obtain ⟨u, v, j, r, hred, hrup⟩ := reduction hR
  obtain ⟨i, hi, t, ht, hc, hu, hv, hr, hpt⟩ := cover hred
  obtain ⟨S, P, hs, hh, ha⟩ := h i hi
  apply root_covered (rootK i) (rootK_inv i hi) S P hs hh ha t ht hpt
  rw [hc]; unfold Bad; rw [hu, hv, hr]
  exact ⟨hred, hrup⟩

end Cayley.Pack

end
