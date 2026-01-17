import Noperthedron.Nopert

namespace Nopert
open Real

local macro "⋃ᶠ " x:ident " ∈ " s:term ", " f:term : term =>
  `(Finset.biUnion $s (fun $x => $f))

noncomputable
def Cpt : Fin 3 → ℝ³
| 0 => C1R
| 1 => C2R
| 2 => C3R

noncomputable
def nopertPt (k ℓ : ℕ) (i : Fin 3) :=
  (-1)^ℓ • RzL (2 * π * (k : ℝ) / 15) (Cpt i)

noncomputable
def nopertList : List ℝ³ := do
  let ℓ ← List.range 2
  let i ← [0, 1, 2]
  let k ← List.range 15
  pure (nopertPt k ℓ i)

noncomputable
def monadicNopertVerts : Set ℝ³ :=
  ⋃ ℓ ∈ Finset.range 2,
  ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)),
  ⋃ k ∈ Finset.range 15,
  {nopertPt k ℓ i}

lemma nopert_list_length : nopertList.length = 90 := by
  simp [nopertList]

lemma nopert_list_test_0 : nopertList[0] = nopertPt 0 0 0 := by
  simp [nopertList, List.range, List.range.loop]

lemma nopert_list_test_1 : nopertList[1] = nopertPt 1 0 0 := by
  simp [nopertList, List.range, List.range.loop]

lemma nopert_list_test_17 : nopertList[17] = nopertPt 2 0 1 := by
  simp [nopertList, List.range, List.range.loop]

lemma nopert_list_test_62 : nopertList[62] = nopertPt 2 1 1 := by
  simp [nopertList, List.range, List.range.loop]

lemma flat_map_finset {α β : Type} [DecidableEq α] [DecidableEq β] (xss : List α) (f : α → List β) :
    (xss.flatMap f).toFinset = ⋃ i ∈ xss, (↑(f i).toFinset : Set β) := by
  match xss with
  | [] => simp
  | h::tl =>
    simp only [List.flatMap_cons, List.toFinset_append, Finset.coe_union,
       List.mem_cons, Set.iUnion_iUnion_eq_or_left]
    congr; rw [flat_map_finset]

lemma nopert_list_eq_monadic_nopert_verts :
    nopertList.toFinset = monadicNopertVerts := by
  simp only [nopertList, List.bind_eq_flatMap, flat_map_finset, monadicNopertVerts]
  simp

lemma union_two {α : Type} [DecidableEq α] (g : ℕ → α) : ⋃ ℓ ∈ Finset.range 2, {g ℓ} = {g 0, g 1}  := by
  simp [Finset.range_add_one]

lemma ell_flips_sign (k : ℕ) (i : Fin 3) : nopertPt k 1 i = -nopertPt k 0 i := by
  simp [nopertPt]

def pointsymmetrize' (vs : Set ℝ³) : Set ℝ³ := vs ∪ vs.image (-·)

lemma pointsymmetrize'_singleton (v : ℝ³) : pointsymmetrize' {v} = {v, -v} := by
  simp [pointsymmetrize']
  rw [Set.pair_comm]

lemma pointsymmetrize'_union (ι : Type*) (j : Set ι) (S : ι → Set ℝ³) :
    pointsymmetrize' (⋃ i ∈ j, S i) = ⋃ i ∈ j, pointsymmetrize' (S i) := by
  simp [pointsymmetrize']
  ext x
  constructor
  · intro hx; simp_all; rcases hx with h | h
    · obtain ⟨i, hi, hi2⟩ := h; use i, hi; left; exact hi2
    · obtain ⟨i, hi, hi2⟩ := h; use i, hi; right; exact hi2
  · intro hx; simp_all; obtain ⟨i, hi, hi2⟩ := hx; rcases hi2 with h | h
    · left; use i, hi
    · right; use i, hi

lemma pointsymmetrize'_union_finset (ι : Type*) (j : Finset ι) (S : ι → Set ℝ³) :
    pointsymmetrize' (⋃ i ∈ j, S i) = ⋃ i ∈ j, pointsymmetrize' (S i) := by
  exact pointsymmetrize'_union ι j S

lemma pointsymmetrize_finset (S : Finset ℝ³) : pointsymmetrize S = pointsymmetrize' S := by
  simp [pointsymmetrize, pointsymmetrize']

lemma Finset.image_eq_biUnion {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) :
    s.image f = s.biUnion (fun i => {f i}) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_singleton]
  tauto

lemma nopert_pt_eq_c15 (i : Fin 3) :
    ⋃ k ∈ Finset.range 15, {nopertPt k 0 i} = C15 (Cpt i) := by
  simp only [C15]
  rw [Finset.image_eq_biUnion]
  simp only [Finset.coe_biUnion,   Finset.coe_singleton]
  change ⋃ k ∈ Finset.range 15, {nopertPt k 0 i} = ⋃ x ∈ (Finset.range 15), {(RzL (2 * π * ↑x / 15)) (Cpt i)}
  apply Set.iUnion_congr
  intro n
  ext v
  simp only [Finset.mem_range, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
    and_congr_right_iff]
  intro hn
  suffices h : nopertPt n 0 i = (RzL (2 * π * ↑n / 15)) (Cpt i) by
    rw [h]
  simp [nopertPt]

lemma monadic_half_eq_half_nopert_verts :
    ↑halfNopertVerts = ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ k ∈ Finset.range 15, {nopertPt k 0 i} := by
  simp only [ Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.iUnion_iUnion_eq_or_left, Set.iUnion_iUnion_eq_left]
  change (↑halfNopertVerts : Set ℝ³) =
    (⋃ k ∈ Finset.range 15, {nopertPt k 0 0}) ∪
    ((⋃ k ∈ Finset.range 15, {nopertPt k 0 1}) ∪
     (⋃ k ∈ Finset.range 15, {nopertPt k 0 2}))
  repeat rw [nopert_pt_eq_c15]
  simp [halfNopertVerts, Cpt]

lemma monadic_nopert_verts_eq_nopert_verts :
    nopertVerts = monadicNopertVerts := by
  unfold nopertVerts monadicNopertVerts
  have :=
    calc ⋃ ℓ ∈ Finset.range 2, ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ k ∈ Finset.range 15, {nopertPt k ℓ i}
    _ = ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ ℓ ∈ Finset.range 2, ⋃ k ∈ Finset.range 15, {nopertPt k ℓ i} := by
      rw [Set.iUnion₂_comm]
    _ = ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ k ∈ Finset.range 15, ⋃ ℓ ∈ Finset.range 2, {nopertPt k ℓ i} := by
       conv => enter [1, 1, i, 1, h]; rw [Set.iUnion₂_comm]
    _ = ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ k ∈ Finset.range 15, {nopertPt k 0 i, nopertPt k 1 i} := by
       conv => enter [1, 1, i, 1, _, 1, k, 1, _]; rw [union_two (nopertPt k · i)]
    _ = ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ k ∈ Finset.range 15, {nopertPt k 0 i, -nopertPt k 0 i} := by
       conv => enter [1, 1, i, 1, _, 1, k, 1, _]; rw [ell_flips_sign]
    _ = ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ k ∈ Finset.range 15, pointsymmetrize' {nopertPt k 0 i} := by
       conv => enter [1, 1, i, 1, _, 1, k, 1, _]; rw [← pointsymmetrize'_singleton];
    _ = ⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), pointsymmetrize' (⋃ k ∈ Finset.range 15,  {nopertPt k 0 i}) := by
       conv => enter [1, 1, i, 1, _]; rw [← pointsymmetrize'_union_finset];
    _ = pointsymmetrize' (⋃ i ∈ ({0, 1, 2} : Set (Fin 3)), ⋃ k ∈ Finset.range 15,  {nopertPt k 0 i}) := by
       rw [← pointsymmetrize'_union];
  rw [pointsymmetrize_finset, this]; congr 1
  exact monadic_half_eq_half_nopert_verts

/-
This is the main result of this file.
-/
theorem nopert_list_eq_nopert_verts :
    nopertList.toFinset = nopertVerts := by
  have : nopertList.toFinset = (↑(nopertVerts) : Set ℝ³):= by
     rw [nopert_list_eq_monadic_nopert_verts,
         monadic_nopert_verts_eq_nopert_verts]
  exact Finset.coe_inj.mp this
