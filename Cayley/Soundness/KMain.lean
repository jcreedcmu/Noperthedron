module

public import Cayley.Soundness.KTreeSound
public import Cayley.Soundness.Reduction

@[expose] public section

/-!
# The main soundness theorem of the kernel checker

If each of the 15 root boxes carries a checked skeleton whose holes are checked hole-free
subtrees, then the Noperthedron is not Rupert.
-/

namespace Cayley

open Cayley.Pack

open Cayley.Checker Noperthedron Real
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

theorem rootBox_chart (i : ℕ) :
    (rootBox i).chart = (if i < 3 then i + 1 else if i < 9 then 0 else 4) ∧
      (rootBox i).face = (if i < 3 then 0 else if i < 9 then i - 3 else i - 9) := by
  simp only [rootBox]; split_ifs <;> exact ⟨rfl, rfl⟩

/-- The points of root box `i`: `u ∈ [0,1]`, `v ∈ [0,1/2]`, two coordinates in `[-1,1]`, and
the last in `[-1,1]`, `[0,1]` or `[0,2]`. -/
theorem rootBox_mem (i : ℕ) (hi : i < 15) (X : Fin 5 → ℝ) (hu0 : 0 ≤ X 0) (hu1 : X 0 ≤ 1)
    (hv0 : 0 ≤ X 1) (hv1 : X 1 ≤ 1 / 2) (h2 : |X 2| ≤ 1) (h3 : |X 3| ≤ 1)
    (h4 : if i < 3 then |X 4| ≤ 1 else 0 ≤ X 4 ∧ X 4 ≤ (if i < 9 then 1 else 2)) :
    X ∈ (rootBox i).pts := by
  rw [abs_le] at h2 h3
  intro k
  rw [abs_le]
  interval_cases i <;> simp only [Nat.reduceLT, ↓reduceIte, abs_le] at h4 <;> fin_cases k <;>
    simp [rootBox] <;> constructor <;> linarith

theorem rootBox_inv (i : ℕ) (hi : i < 15) : Inv (rootBox i) := by
  interval_cases i <;>
    exact ⟨by decide, by decide, rfl, rfl, fun k => by fin_cases k <;> decide,
      fun k => by fin_cases k <;> decide⟩

/-! ## Coverage -/

theorem cover {u v : ℝ} {j : ℕ} {r : Fin 3 → ℝ} (hred : Reduced u v j r) :
    ∃ i < 15, ∃ X ∈ (rootBox i).pts, (rootBox i).chart = j ∧ X 0 = u ∧ X 1 = v ∧
      rOf (kblow j) (rootBox i).face X = r ∧ PtOK (rootBox i).chart (rootBox i).face X := by
  have hu1 : u ≤ 1 := by nlinarith [hred.disk, sq_nonneg v, hred.u_nonneg]
  have hv : v ≤ 1 / 2 := by linarith [hred.wedge]
  have hu0 := hred.u_nonneg
  have hv0 := hred.v_nonneg
  have hrb := hred.rb
  have hj := hred.j_lt
  by_cases hj04 : j = 0 ∨ j = 4
  · obtain ⟨f, hf, ρ, s0, s1, hρ0, hρR, hs0, hs1, hr⟩ := exists_face r _ hrb
    have hkb : kblow j = true := by rcases hj04 with rfl | rfl <;> rfl
    -- root `3 + f` (chart 0) or `9 + f` (chart 4)
    obtain ⟨i, hi, hi3, hi9⟩ : ∃ i < 15, ¬ i < 3 ∧ (i < 9 ↔ j = 0) ∧
        (if i < 9 then i - 3 else i - 9) = f ∧ (if i < 9 then 0 else 4) = j := by
      rcases hj04 with rfl | rfl
      · exact ⟨3 + f, by omega, by omega, by omega, by split_ifs <;> omega, by split_ifs <;> omega⟩
      · exact ⟨9 + f, by omega, by omega, by omega, by split_ifs <;> omega, by split_ifs <;> omega⟩
    obtain ⟨hi9, hface, hchart⟩ := hi9
    obtain ⟨hc, hfc⟩ := rootBox_chart i
    simp only [hi3, ↓reduceIte, hface, hchart] at hc hfc
    have hρ : ρ ≤ (if i < 9 then 1 else 2) := by
      rcases hj04 with rfl | rfl
      · simpa [hi9] using hρR
      · simpa [hi9] using hρR
    refine ⟨i, hi, ![u, v, s0, s1, ρ], rootBox_mem i hi _ hu0 hu1 hv0 hv hs0 hs1 ?_, hc, rfl, rfl,
      ?_, ?_⟩
    · simpa [hi3] using ⟨hρ0, hρ⟩
    · simpa [hfc, hkb, rOf] using hr
    · rw [hc, hfc]
      refine ⟨by simpa using hred.disk, fun k => ?_, fun _ => ?_⟩
      · have : rOf (kblow j) f ![u, v, s0, s1, ρ] = r := by simpa [hkb, rOf] using hr
        rw [this]; exact (hrb k).trans (by split_ifs <;> norm_num)
      · exact ⟨hρ0, hρ.trans (by split_ifs <;> norm_num), hs0, hs1⟩
  · push Not at hj04
    have hi : j - 1 < 3 := by omega
    have hkb : kblow j = false := by simp [kblow, hj04.1, hj04.2]
    have hr1 : ∀ k, |r k| ≤ 1 := fun k => by have := hrb k; simpa [hj04.2] using this
    obtain ⟨hc, hfc⟩ := rootBox_chart (j - 1)
    simp only [hi, ↓reduceIte] at hc hfc
    have hjc : (rootBox (j - 1)).chart = j := by rw [hc]; omega
    have hrr : rOf (kblow j) (rootBox (j - 1)).face ![u, v, r 0, r 1, r 2] = r := by
      rw [hkb]; funext k; fin_cases k <;> simp [rOf]
    refine ⟨j - 1, by omega, ![u, v, r 0, r 1, r 2],
      rootBox_mem _ (by omega) _ hu0 hu1 hv0 hv (hr1 0) (hr1 1) (by simpa [hi] using hr1 2), hjc,
      rfl, rfl, hrr, ?_⟩
    rw [hjc]
    refine ⟨by simpa using hred.disk, fun k => ?_, fun h => by simp [hkb] at h⟩
    rw [hrr]; linarith [hr1 k]

/-! ## Assembly -/

theorem AllOK_mem {P : List (Box × Tree)} (h : AllOK P) :
    ∀ p ∈ P, checkTree false p.1 p.2 = true := by
  induction P with
  | nil => simp
  | cons q P ih =>
    obtain ⟨b, t⟩ := q
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact ih h.2 p hp

/-- A root skeleton whose holes are checked hole-free subtrees covers its box. -/
theorem root_covered (b : Box) (hb : Inv b) (S : Tree) (P : List (Box × Tree))
    (hs : checkTree true b S = true) (hh : holes b S = P.map Prod.fst) (ha : AllOK P) :
    Covered b := by
  intro X hX hpt hbad
  obtain ⟨x, hx, hix, hc, hf, hm⟩ := walk true S b hb hs X hX hpt hbad
  rw [hh, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  apply covered_of_check p.1 hix p.2 (AllOK_mem ha p hp) X hm
  · rw [hc, hf]; exact hpt
  · rw [hc, hf]; exact hbad

/-- The certificate facts for one root box. -/
def RootOK (i : ℕ) : Prop :=
  ∃ S : Tree, ∃ P : List (Box × Tree),
    checkTree true (rootBox i) S = true ∧ holes (rootBox i) S = P.map Prod.fst ∧ AllOK P

/-- **Main soundness theorem.** Certificates for the 15 root boxes refute Rupertness. -/
theorem kernel_sound (h : ∀ i < 15, RootOK i) : ¬ IsRupert exactVerts := by
  intro hR
  obtain ⟨u, v, j, r, hred, hrup⟩ := reduction hR
  obtain ⟨i, hi, X, hX, hc, hu, hv, hr, hpt⟩ := cover hred
  obtain ⟨S, P, hs, hh, ha⟩ := h i hi
  apply root_covered (rootBox i) (rootBox_inv i hi) S P hs hh ha X hX hpt
  rw [hc]; unfold Bad; rw [hu, hv, hr]
  exact ⟨hred, hrup⟩

end Cayley

end
