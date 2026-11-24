module

public import Noperthedron.PointSym

public section


/-
This file more or less captures Proposition 2 from
"An algorithmic approach to Rupert's problem"
[Steininger, Yurkevich 2021]
https://arxiv.org/pdf/2112.13754

The crux is that if a polyhedron (or indeed any convex set) S is
pointsymmetric (i.e. invariant under x ↦ -x) then the question of
whether S is Rupert can, without loss, be analyzed by only considering
rotations, and ignoring translations.
-/

open scoped Matrix

/--
Suppose A and B are both pointsymmetric subsets of ℝ². Suppose B is convex.
If some translate of A is contained in B, then A is contained in B.
-/
theorem common_center {A B : Set ℝ²} (psa : PointSym A) (psb : PointSym B)
    (b_convex : Convex ℝ B)
    (v : ℝ²) (hin : (· + v) '' A ⊆ B) : A ⊆ B := by
  intro a ha
  have h1 : a + v ∈ B := hin ⟨a, ha, rfl⟩
  have h2 : a - v ∈ B := by
    have han : -a ∈ A := psa a ha
    have hnav : -a + v ∈ B := hin ⟨-a, han, rfl⟩
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using psb (-a + v) hnav
  have segment_sub_b := convex_iff_segment_subset.mp b_convex h1 h2
  exact segment_sub_b (mem_segment_add_sub a v)

end
