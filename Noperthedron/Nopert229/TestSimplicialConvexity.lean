import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation

open scoped BigOperators RealInnerProductSpace

theorem inner_ge_of_triangle_vertices
    (V : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (v : EuclideanSpace ℝ (Fin 3))
    (c : ℝ)
    (hc : 0 ≤ c)
    (hV : ∀ j : Fin 3, c * ‖V j‖ ≤ inner ℝ (V j) v)
    (w : Fin 3 → ℝ)
    (hw_nonneg : ∀ j, 0 ≤ w j) :
    c * ‖∑ j, w j • V j‖ ≤ inner ℝ (∑ j, w j • V j) v := by
  have h_inner : inner ℝ (∑ j, w j • V j) v = ∑ j, w j * inner ℝ (V j) v := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j _
    rw [inner_smul_left, RCLike.conj_to_real]
  have h_norm : ‖∑ j, w j • V j‖ ≤ ∑ j, w j * ‖V j‖ := by
    have h1 := norm_sum_le Finset.univ (fun j => w j • V j)
    refine h1.trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul, Real.norm_of_nonneg (hw_nonneg j)]
  have h_bound : c * (∑ j, w j * ‖V j‖) ≤ ∑ j, w j * inner ℝ (V j) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc c * (w j * ‖V j‖) = w j * (c * ‖V j‖) := by ring
      _ ≤ w j * inner ℝ (V j) v := mul_le_mul_of_nonneg_left (hV j) (hw_nonneg j)
  rw [h_inner]
  calc c * ‖∑ j, w j • V j‖ ≤ c * (∑ j, w j * ‖V j‖) := mul_le_mul_of_nonneg_left h_norm hc
    _ ≤ ∑ j, w j * inner ℝ (V j) v := h_bound

theorem inner_ge_of_triangle_unit
    (V : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (v : EuclideanSpace ℝ (Fin 3))
    (c : ℝ)
    (hc : 0 ≤ c)
    (hV : ∀ j : Fin 3, c * ‖V j‖ ≤ inner ℝ (V j) v)
    (a : EuclideanSpace ℝ (Fin 3))
    (ha_norm : ‖a‖ = 1)
    (w : Fin 3 → ℝ)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (ha_rep : a = ∑ j, w j • V j) :
    c ≤ inner ℝ a v := by
  have h := inner_ge_of_triangle_vertices V v c hc hV w hw_nonneg
  rw [← ha_rep, ha_norm, mul_one] at h
  exact h
