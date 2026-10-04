module

public import Noperthedron.Atlas.CayleyEdgeCertificate

@[expose] public section


/-!
# Projective view triangles

Viewing directions are represented by projective triangles on the plane
x + y + z = 1 (`Triangle`, `InTriangle`), subdivided by `split` (three corner
triangles and the central one). `linearValue` bounds linear functionals
over a triangle by their corner values.

(Extracted, with only what the certificates use, from the earlier snub-cube
proof attempt.)
-/

namespace Noperthedron.Atlas.ProjectiveView

open Noperthedron.Atlas
open CayleyEdgeCertificate

abbrev Vector (R : Type) := Fin 3 → R
abbrev Triangle (R : Type) := Fin 3 → Vector R

def affinePoint (triangle : Triangle ℝ) (weight : Vector ℝ) : Vector ℝ :=
  fun c => ∑ i, weight i * triangle i c

def InTriangle (triangle : Triangle ℝ) (point : Vector ℝ) : Prop :=
  ∃ weight : Vector ℝ, (∀ i, 0 ≤ weight i) ∧
    (∑ i, weight i) = 1 ∧ point = affinePoint triangle weight

def linearValue (point coefficient : Vector ℝ) : ℝ :=
  point 0 * coefficient 0 + point 1 * coefficient 1 +
    point 2 * coefficient 2

theorem linearValue_le_of_mem {triangle : Triangle ℝ} {point : Vector ℝ}
    {coefficient : Vector ℝ} {bound : ℝ}
    (hmem : InTriangle triangle point)
    (hbound : ∀ i, linearValue (triangle i) coefficient ≤ bound) :
    linearValue point coefficient ≤ bound := by
  obtain ⟨weight, hnonneg, hsum, hpoint⟩ := hmem
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  have h0 := mul_le_mul_of_nonneg_left (hbound 0) (hnonneg 0)
  have h1 := mul_le_mul_of_nonneg_left (hbound 1) (hnonneg 1)
  have h2 := mul_le_mul_of_nonneg_left (hbound 2) (hnonneg 2)
  have hboundsum : weight 0 * bound + weight 1 * bound +
      weight 2 * bound = bound := by
    calc
      _ = (weight 0 + weight 1 + weight 2) * bound := by ring
      _ = bound := by rw [hsum3]; ring
  rw [hpoint]
  have heq : linearValue (affinePoint triangle weight) coefficient =
      weight 0 * linearValue (triangle 0) coefficient +
        weight 1 * linearValue (triangle 1) coefficient +
        weight 2 * linearValue (triangle 2) coefficient := by
    simp [linearValue, affinePoint, Fin.sum_univ_three]
    ring
  rw [heq]
  linarith

theorem le_linearValue_of_mem {triangle : Triangle ℝ} {point : Vector ℝ}
    {coefficient : Vector ℝ} {bound : ℝ}
    (hmem : InTriangle triangle point)
    (hbound : ∀ i, bound ≤ linearValue (triangle i) coefficient) :
    bound ≤ linearValue point coefficient := by
  obtain ⟨weight, hnonneg, hsum, hpoint⟩ := hmem
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  have h0 := mul_le_mul_of_nonneg_left (hbound 0) (hnonneg 0)
  have h1 := mul_le_mul_of_nonneg_left (hbound 1) (hnonneg 1)
  have h2 := mul_le_mul_of_nonneg_left (hbound 2) (hnonneg 2)
  have hboundsum : weight 0 * bound + weight 1 * bound +
      weight 2 * bound = bound := by
    calc
      _ = (weight 0 + weight 1 + weight 2) * bound := by ring
      _ = bound := by rw [hsum3]; ring
  rw [hpoint]
  have heq : linearValue (affinePoint triangle weight) coefficient =
      weight 0 * linearValue (triangle 0) coefficient +
        weight 1 * linearValue (triangle 1) coefficient +
        weight 2 * linearValue (triangle 2) coefficient := by
    simp [linearValue, affinePoint, Fin.sum_univ_three]
    ring
  rw [heq]
  linarith

def midpoint (a b : Vector ℚ) : Vector ℚ := fun c => (a c + b c) / 2

/-- The three corner triangles followed by the central triangle. -/
def split (triangle : Triangle ℚ) : Fin 4 → Triangle ℚ := ![
  ![triangle 0, midpoint (triangle 0) (triangle 1),
    midpoint (triangle 0) (triangle 2)],
  ![midpoint (triangle 0) (triangle 1), triangle 1,
    midpoint (triangle 1) (triangle 2)],
  ![midpoint (triangle 0) (triangle 2),
    midpoint (triangle 1) (triangle 2), triangle 2],
  ![midpoint (triangle 0) (triangle 1),
    midpoint (triangle 1) (triangle 2),
    midpoint (triangle 2) (triangle 0)]]

def toReal (triangle : Triangle ℚ) : Triangle ℝ :=
  fun i c => triangle i c

@[simp] theorem toReal_midpoint (a b : Vector ℚ) (c : Fin 3) :
    (midpoint a b c : ℝ) = ((a c : ℝ) + (b c : ℝ)) / 2 := by
  norm_num [midpoint]

private theorem corner_zero {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hpoint : point = affinePoint (toReal triangle) weight)
    (hlarge : 1 / 2 ≤ weight 0) :
    InTriangle (toReal (split triangle 0)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ := ![2 * weight 0 - 1, 2 * weight 1, 2 * weight 2]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2]
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * (triangle 0 c : ℝ)) hsum3
    nlinarith

private theorem corner_one {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hpoint : point = affinePoint (toReal triangle) weight)
    (hlarge : 1 / 2 ≤ weight 1) :
    InTriangle (toReal (split triangle 1)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ := ![2 * weight 0, 2 * weight 1 - 1, 2 * weight 2]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2]
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * (triangle 1 c : ℝ)) hsum3
    nlinarith

private theorem corner_two {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hpoint : point = affinePoint (toReal triangle) weight)
    (hlarge : 1 / 2 ≤ weight 2) :
    InTriangle (toReal (split triangle 2)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ := ![2 * weight 0, 2 * weight 1, 2 * weight 2 - 1]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2]
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * (triangle 2 c : ℝ)) hsum3
    nlinarith

private theorem central {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hsmall0 : weight 0 ≤ 1 / 2) (hsmall1 : weight 1 ≤ 1 / 2)
    (hsmall2 : weight 2 ≤ 1 / 2)
    (hpoint : point = affinePoint (toReal triangle) weight) :
    InTriangle (toReal (split triangle 3)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ :=
    ![1 - 2 * weight 2, 1 - 2 * weight 0, 1 - 2 * weight 1]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * ((triangle 0 c : ℝ) +
      triangle 1 c + triangle 2 c)) hsum3
    nlinarith

/-- The four midpoint children cover their parent, including all shared
boundaries. -/
theorem mem_split {triangle : Triangle ℚ} {point : Vector ℝ}
    (h : InTriangle (toReal triangle) point) :
    ∃ child : Fin 4, InTriangle (toReal (split triangle child)) point := by
  obtain ⟨weight, hnonneg, hsum, hpoint⟩ := h
  by_cases h0 : 1 / 2 ≤ weight 0
  · exact ⟨0, corner_zero hnonneg hsum hpoint h0⟩
  · by_cases h1 : 1 / 2 ≤ weight 1
    · exact ⟨1, corner_one hnonneg hsum hpoint h1⟩
    · by_cases h2 : 1 / 2 ≤ weight 2
      · exact ⟨2, corner_two hnonneg hsum hpoint h2⟩
      · exact ⟨3, central hnonneg hsum (le_of_not_ge h0)
          (le_of_not_ge h1) (le_of_not_ge h2) hpoint⟩

end Noperthedron.Atlas.ProjectiveView

end
