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

  sorry
