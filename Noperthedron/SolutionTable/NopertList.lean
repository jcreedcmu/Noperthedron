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

def bigUnion {α : Type} [DecidableEq α] (ℓ : List (Finset α)) : Finset α :=
  ℓ.foldl (fun s t => s ∪ t) ∅

lemma flat_map_finset {α β : Type} [DecidableEq β] (xss : List α) (f : α → List β) :
    (xss.flatMap f).toFinset = bigUnion (xss.map (fun x => (f x).toFinset)) := by
    sorry

lemma nopert_list_eq_nopert_verts (v : ℝ³) :
    nopertList.toFinset = nopertVerts := by
  simp only [nopertList, List.pure_def, List.bind_eq_flatMap]
  simp only [flat_map_finset]
  simp [bigUnion, List.foldl_map]
  change List.foldl
      (fun s ℓ ↦
        s ∪
          (List.foldl (fun s k ↦ insert (nopertPt k ℓ 0) s) ∅ (List.range 15) ∪
            (List.foldl (fun s k ↦ insert (nopertPt k ℓ 1) s) ∅ (List.range 15) ∪
              List.foldl (fun s k ↦ insert (nopertPt k ℓ 2) s) ∅ (List.range 15))))
      ∅ (List.range 2) =
    nopertVerts

  sorry
