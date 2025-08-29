import Rupert.Basic
import Rupert.Set
import NegativeRupert.RotRupert

def PointSym {n : ℕ} (A : Set (Fin n → ℝ)) : Prop :=
 ∀ x ∈ A, -x ∈ A

lemma segment_lemma (k : ℝ) (a v : ℝ²) : k • a + k • v + k • (a - v) = (k * 2) • a := by
 rw [smul_sub]
 calc (k • a + k • v) + (k • a - k • v)
 _ = k • a + (k • v + (k • a - k • v)) := by rw [add_assoc]
 _ = k • a + (k • v + ((-(k • v)) + k • a)) := by nth_rw 5 [add_comm]; rfl
 _ = k • a + ((k • v + (-(k • v))) + k • a) := by nth_rw 1 [add_assoc]
 _ = k • a + k • a := by rw [add_neg_cancel, zero_add]
 _ = (k * 2) • a := by rw [← add_smul, ← mul_two]

/--
Suppose A and B are both pointsymmetric subsets of ℝ². Suppose B is convex.
If some translate of A is contained in B, then A is contained in B.
-/
theorem common_center {A B : Set ℝ²} (psa : PointSym A) (psb : PointSym B)
    (b_convex : Convex ℝ B)
    (v : ℝ²) (hin : (· + v) '' A ⊆ B) : A ⊆ B := by
  intro a ha
  have h1 : a + v ∈ B := by
    grind only [= Set.mem_image, = Set.subset_def]
  have h2 : a - v ∈ B := by
    have han : -a ∈ A := psa a ha
    have hnav : -a + v ∈ B := by grind only [= Set.mem_image, = Set.subset_def]
    have hnn : -(-a + v) ∈ B := psb (-a + v) hnav
    have e : -(-a + v) = a - v := by grind only
    rw [e] at hnn
    exact hnn
  have segment_sub_b := convex_iff_segment_subset.mp b_convex h1 h2
  have a_in_segment : a ∈ segment ℝ (a + v) (a - v) := by
    unfold segment
    simp only [smul_add, exists_and_left, Set.mem_setOf_eq]
    refine ⟨ 1/2, ?_, 1/2, ?_, ?_, ?_ ⟩
    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    · grind
    · rw [segment_lemma (1/2) a v]
      norm_num
  exact segment_sub_b a_in_segment

/--
If a set is point symmetric, then being rupert implies being purely rotationally rupert.
-/
theorem rupert_implies_rot_rupert {S : Set ℝ³} (s_sym : PointSym S)
    (r : IsRupertSet S) : IsRotRupertSet S := by
  unfold IsRupertSet IsRupertPair at r
  obtain ⟨inn, inn_so3, off, out, out_so3, v⟩ := r
  use inn, inn_so3, out, out_so3
  intro inner_shadow outer_shadow
  let inner_shadow' := {x | ∃ p ∈ S, off + proj_xy (inn.mulVec p) = x}
  change closure inner_shadow' ⊆ interior outer_shadow at v
  refine common_center ?_ ?_ ?_ off ?_
  · sorry
  · sorry
  · sorry
  · sorry
