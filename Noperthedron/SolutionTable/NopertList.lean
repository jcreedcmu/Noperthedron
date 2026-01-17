import Noperthedron.Nopert

namespace Nopert
open Real

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
def monadicNopertVerts : Finset ℝ³ :=
  Finset.biUnion (Finset.range 2) (fun ℓ =>
  Finset.biUnion {0, 1, 2} (fun i =>
  Finset.biUnion (Finset.range 15) (fun k =>
  {nopertPt k ℓ i})))

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
    (xss.flatMap f).toFinset = (xss.toFinset).biUnion  (f · |>.toFinset) := by
  match xss with
  | [] => simp
  | h::tl =>
    simp only [List.flatMap_cons, List.toFinset_append, List.toFinset_cons, Finset.biUnion_insert];
    congr; rw [flat_map_finset]

lemma nopert_list_eq_monadic_nopert_verts :
    nopertList.toFinset = monadicNopertVerts := by
  simp only [nopertList, List.pure_def, List.bind_eq_flatMap, flat_map_finset]
  repeat rw [List.toFinset_range]
  simp [monadicNopertVerts]
