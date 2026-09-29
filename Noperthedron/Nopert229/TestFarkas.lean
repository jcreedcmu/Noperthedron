module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fin.VecNotation
public import Noperthedron.SnubCube.ProjectiveView
public import Noperthedron.Nopert229.AtlasProjectiveView

@[expose] public section

open scoped BigOperators RealInnerProductSpace
open Noperthedron.SnubCube.ProjectiveView

namespace Noperthedron.Nopert229.TestFarkas

abbrev Vec3 := Fin 3 → ℝ

def dot (a b : Vec3) : ℝ :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

theorem dot_zero_right (a : Vec3) : dot a 0 = 0 := by
  simp [dot]

theorem dot_add_right (a b c : Vec3) : dot a (b + c) = dot a b + dot a c := by
  simp [dot]
  ring

theorem dot_smul_right (a b : Vec3) (s : ℝ) : dot a (s • b) = s * dot a b := by
  simp [dot]
  ring

theorem dot_sum_right {ι : Type*} [Fintype ι] (a : Vec3) (f : ι → Vec3) :
    dot a (∑ i, f i) = ∑ i, dot a (f i) := by
  classical
  induction' (Finset.univ : Finset ι) using Finset.induction_on with x s hx ih
  · simp [dot]
  · rw [Finset.sum_insert hx, dot_add_right, ih, Finset.sum_insert hx]

theorem sum_eq_zero_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ f i) (hsum : ∑ i ∈ s, f i = 0) :
    ∀ i ∈ s, f i = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum

theorem farkas_orthogonal {ι : Type*} [Fintype ι]
    (v : ι → Vec3) (lam : ι → ℝ)
    (hpos : ∀ i, 0 < lam i)
    (hsum : (∑ i, lam i • v i) = 0)
    (u : Vec3) (hu : ∀ i, 0 ≤ dot u (v i)) :
    ∀ i, dot u (v i) = 0 := by
  have hdot : dot u (∑ i, lam i • v i) = 0 := by
    rw [hsum, dot_zero_right]
  rw [dot_sum_right] at hdot
  have hterm_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ dot u (lam i • v i) := by
    intro i _
    rw [dot_smul_right]
    exact mul_nonneg (le_of_lt (hpos i)) (hu i)
  have hall_zero := sum_eq_zero_of_nonneg Finset.univ _ hterm_nonneg hdot
  intro i
  have h_i := hall_zero i (Finset.mem_univ i)
  rw [dot_smul_right] at h_i
  exact (mul_eq_zero.mp h_i).resolve_left (ne_of_gt (hpos i))

def det3 (a b c : Vec3) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) -
  a 1 * (b 0 * c 2 - b 2 * c 0) +
  a 2 * (b 0 * c 1 - b 1 * c 0)

theorem eq_zero_of_dot_basis (v0 v1 v2 : Vec3) (hdet : det3 v0 v1 v2 ≠ 0)
    (u : Vec3) (h0 : dot u v0 = 0) (h1 : dot u v1 = 0) (h2 : dot u v2 = 0) :
    u = 0 := by
  apply funext
  intro c
  fin_cases c
  · have hx : u 0 * det3 v0 v1 v2 =
        (v1 1 * v2 2 - v1 2 * v2 1) * dot u v0 +
        (v0 2 * v2 1 - v0 1 * v2 2) * dot u v1 +
        (v0 1 * v1 2 - v0 2 * v1 1) * dot u v2 := by
      simp [dot, det3]
      ring
    rw [h0, h1, h2] at hx
    simp at hx
    exact hx.resolve_right hdet
  · have hy : u 1 * det3 v0 v1 v2 =
        (v1 2 * v2 0 - v1 0 * v2 2) * dot u v0 +
        (v0 0 * v2 2 - v0 2 * v2 0) * dot u v1 +
        (v0 2 * v1 0 - v0 0 * v1 2) * dot u v2 := by
      simp [dot, det3]
      ring
    rw [h0, h1, h2] at hy
    simp at hy
    exact hy.resolve_right hdet
  · have hz : u 2 * det3 v0 v1 v2 =
        (v1 0 * v2 1 - v1 1 * v2 0) * dot u v0 +
        (v0 1 * v2 0 - v0 0 * v2 1) * dot u v1 +
        (v0 0 * v1 1 - v0 1 * v1 0) * dot u v2 := by
      simp [dot, det3]
      ring
    rw [h0, h1, h2] at hz
    simp at hz
    exact hz.resolve_right hdet

theorem linearValue_sum_coords (p : Vector ℝ) :
    linearValue p ![1, 1, 1] = p 0 + p 1 + p 2 := by
  simp [linearValue]

theorem upperWedge_sum_coords {u : Vector ℝ}
    (hu : InTriangle (toReal AtlasProjectiveView.upperWedgeTriangle) u) :
    u 0 + u 1 + u 2 = 1 := by
  obtain ⟨w, _, hwsum, hu_eq⟩ := hu
  have hw3 : w 0 + w 1 + w 2 = 1 := by
    simpa [Fin.sum_univ_three] using hwsum
  rw [hu_eq, ← linearValue_sum_coords]
  have heq : linearValue (affinePoint (toReal AtlasProjectiveView.upperWedgeTriangle) w) ![1, 1, 1] =
      w 0 * linearValue (toReal AtlasProjectiveView.upperWedgeTriangle 0) ![1, 1, 1] +
      w 1 * linearValue (toReal AtlasProjectiveView.upperWedgeTriangle 1) ![1, 1, 1] +
      w 2 * linearValue (toReal AtlasProjectiveView.upperWedgeTriangle 2) ![1, 1, 1] := by
    simp [linearValue, affinePoint, Fin.sum_univ_three]
    ring
  rw [heq]
  have h0 : linearValue (toReal AtlasProjectiveView.upperWedgeTriangle 0) ![1, 1, 1] = 1 := by
    simp [linearValue, AtlasProjectiveView.upperWedgeTriangle, toReal]
  have h1 : linearValue (toReal AtlasProjectiveView.upperWedgeTriangle 1) ![1, 1, 1] = 1 := by
    simp [linearValue, AtlasProjectiveView.upperWedgeTriangle, toReal]
    norm_num
  have h2 : linearValue (toReal AtlasProjectiveView.upperWedgeTriangle 2) ![1, 1, 1] = 1 := by
    simp [linearValue, AtlasProjectiveView.upperWedgeTriangle, toReal]
  rw [h0, h1, h2]
  linarith

theorem ne_zero_of_in_upperWedge {u : Vector ℝ}
    (hu : InTriangle (toReal AtlasProjectiveView.upperWedgeTriangle) u) :
    u ≠ 0 := by
  intro h
  have hsum := upperWedge_sum_coords hu
  have hzero : u 0 + u 1 + u 2 = 0 := by
    rw [h]
    simp
  rw [hzero] at hsum
  norm_num at hsum

end Noperthedron.Nopert229.TestFarkas
