import Noperthedron.SolutionTable.Basic

namespace Noperthedron.Solution

/-
ID,nodeType,nrChildren,IDfirstChild,split,
T1_min,T1_max,V1_min,V1_max,T2_min,T2_max,V2_min,V2_max,A_min,A_max,
P1_index,P2_index,P3_index,Q1_index,Q2_index,Q3_index,
r,sigma_Q,
wx_nominator,wy_nominator,w_denominator,S_index

0,3,4,1,1,0,6451200,0,48384000,0,6451200,0,24268800,-24268800,24268800,,,,,,,,,,,,
-/

/-- Row 245 from `data/solution_tree_300.csv` — the first local leaf. -/
def rowZero : Row := {
  ID := 0, nodeType := 3, nrChildren := 4, IDfirstChild := 1, split := 1,
  interval := Interval.ofIntPose
    { θ₁ := 0, φ₁ := 0, θ₂ := 0,  φ₂ := 0, α := -24268800 }
    { θ₁ := 6451200, φ₁ := 48384000, θ₂ := 6451200, φ₂ := 24268800, α := 24268800 }
    (by decide),
  S_index := 0, wx_numerator := 0, wy_numerator := 0, w_denominator := 0,
  P1_index := 0,
  P2_index := 0,
  P3_index := 0,
  Q1_index := 0,
  Q2_index := 0,
  Q3_index := 0,
  r' := 0, sigma_Q := ⟨0, Finset.insert_eq_self.mp rfl⟩
}

theorem rowZero_contains_tightInterval :
    (tightInterval : Set (Pose ℝ)) ⊆ (rowZero.interval : Set (Pose ℝ)) := by
  intro p hp
  simp only [tightInterval, SetLike.mem_coe, NonemptyInterval.mem_mk] at hp
  simp [Set.mem_Icc, rowZero, Interval.ofIntPose, Interval.minPose, Interval.maxPose]
  show ({ θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -24268800 / DENOMQ } : Pose ℚ).toReal ≤ p ∧
    p ≤ ({ θ₁ := 6451200 / DENOMQ, θ₂ := 6451200 / DENOMQ, φ₁ := 48384000 / DENOMQ,
           φ₂ := 24268800 / DENOMQ, α := 24268800 / DENOMQ } : Pose ℚ).toReal
  obtain ⟨hlo, hhi⟩ := hp
  rw [Pose.le_iff] at hlo hhi
  obtain ⟨h1l, h2l, h3l, h4l, h5l⟩ := hlo
  obtain ⟨h1h, h2h, h3h, h4h, h5h⟩ := hhi
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  refine ⟨?_, ?_⟩ <;> rw [Pose.le_iff]
  · simp only [Pose.toReal, DENOMQ]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith
  · simp only [Pose.toReal, DENOMQ]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith
