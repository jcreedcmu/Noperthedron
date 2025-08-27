import Rupert.Basic

def PointSym (A : Set ℝ²) : Prop :=
 ∀ x ∈ A, -x ∈ A

lemma foo (k : ℝ) (a v : ℝ²) : k • a + k • v + k • (a - v) = (k * 2) • a := by
 rw [smul_sub]
 calc (k • a + k • v) + (k • a - k • v)
 _ = k • a + (k • v + (k • a - k • v)) := by apply add_assoc
 _ = k • a + (k • v + ((-(k • v)) + k • a)) := by nth_rw 5 [add_comm]; rfl
 _ = k • a + ((k • v + (-(k • v))) + k • a) := by nth_rw 1 [add_assoc]
 _ = (k * 2) • a := by sorry


     -- calc (1/2) • a + (1/2) • v + (1/2) • (a - v)
     --       = (1/2) • a + (1/2) • v + ((1/2) • a - (1/2) • v) : by rw smul_sub
     --   ... = (1/2) • a + (1/2) • v + (1/2) • a - (1/2) • v : by rw add_assoc
     --   ... = (1/2) • a + (1/2) • a + ((1/2) • v - (1/2) • v) : by ac_refl
     --   ... = (1/2) • a + (1/2) • a + 0 : by rw sub_self
     --   ... = (1/2 + 1/2) • a : by rw add_smul
     --   ... = 1 • a : by norm_num
     --   ... = a : by rw one_smul

/--
Suppose A and B are both pointsymmetric. Suppose B is convex.
If some translate of A is contained in B, then A is contained in B.
-/
theorem common_center (A B : Set ℝ²) (psa : PointSym A) (psb : PointSym B)
    (b_convex : Convex ℝ B)
    (v : ℝ²) (hin : (· + v) '' A ⊆ B) : A ⊆ B := by
  intro a ha
  have h1 : a + v ∈ B := by
    sorry
  have h2 : a - v ∈ B := by
    sorry
  have z := convex_iff_segment_subset.mp b_convex h1 h2
  have q : a ∈ segment ℝ (a + v) (a - v) := by
    unfold segment
    simp
    refine ⟨ 1/2, ?_, 1/2, ?_, ?_, ?_ ⟩
    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    · grind
    · rw [foo (1/2) a v]


      sorry
  sorry
