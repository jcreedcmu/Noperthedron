module

public import Noperthedron.BalancedSupport.FiniteRotation
public import Noperthedron.BalancedSupport.LocalRigidity
public import Noperthedron.BalancedSupport.AxisFree
public import Noperthedron.BalancedSupport.Rodrigues
public import Noperthedron.Nopert229.SymmetryLocal
public import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
public import Noperthedron.Nopert229.AtlasProjectiveLocalRigidity

@[expose] public section

/-!
# Two-Zone Annular Projective Local Certificates

This module implements the two-zone annular certificate method for ruling out
adversary Rupert poses across challenging projective cells on Candidate #229.

In regions where a single 2D hull contact cannot simultaneously certify the
exact center ($Q = 1$) and satisfy global subdivision constraints without
exceeding the 2D contact hull, the cell is partitioned into two concentric zones
around the 5-fold equality stratum:
1. Inner disk `‖Q - 1‖ ≤ r0`: Certified by strict 2D hull contacts (`defect = 0`),
   where the rotation angle is bounded by `r0`.
2. Outer annulus `r0 ≤ ‖Q - 1‖ ≤ r`: Certified by a defect-tolerant support
   certificate where non-hull support contacts incur a small known defect `defect[j, i]`.
   The annular lower bound `r0 ≤ ‖Q - 1‖` guarantees that the linear first-order
   displacement strictly dominates both the bend remainder and the support defect budget `D`.

Together, `LinearOrder.le_total ‖Q - 1‖ r0` ensures that every pose in the cell
is unconditionally ruled out.
-/

namespace Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

open scoped BigOperators Real RealInnerProductSpace
open Noperthedron.BalancedSupport
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveView AtlasProjectiveEdgeCertificate
open AtlasProjectiveLocalRigidity

/-- A Two-Zone Box pairs an inner strict certificate box with an outer
defect-tolerant certificate box over the same geometric atlas domain. -/
structure TwoZoneBox where
  innerBox : Box
  outerBox : Box
  r0 : ℚ
  defect : Fin 4 → Fin 3 → ℚ
  D : Fin 4 → ℚ

@[mk_iff]
structure TwoZoneBox.Valid (box : TwoZoneBox) : Prop where
  inner_valid : box.innerBox.ViewValid
  compatible_root : box.outerBox.root = box.innerBox.root
  compatible_triangle : box.outerBox.triangle = box.innerBox.triangle
  compatible_chart : box.outerBox.chart = box.innerBox.chart
  compatible_symmetry : box.outerBox.symmetryIndex = box.innerBox.symmetryIndex
  compatible_interval : box.outerBox.interval = box.innerBox.interval
  r0_nonneg : 0 ≤ box.r0
  outer_r_nonneg : 0 ≤ box.outerBox.r
  inner_angle_bound : box.r0 ^ 2 * (1 + box.innerBox.c ^ 2) ≤ 4 * box.innerBox.c ^ 2
  outer_mismatch_bound : box.outerBox.mismatchRadius ≤ box.outerBox.r
  outer_r_le_two : box.outerBox.r ≤ 2
  defect_nonneg : ∀ j i, 0 ≤ box.defect j i
  D_nonneg : ∀ j, 0 ≤ box.D j
  c_nonneg : 0 ≤ box.outerBox.c
  delta_nonneg : 0 ≤ box.outerBox.δ
  B_pos : ∀ j, 0 < (box.outerBox.certificate j).B
  weight_nonneg : ∀ j i, 0 ≤ box.outerBox.weightLower j i
  weight_pos : ∀ j, ∃ i, 0 < box.outerBox.weightLower j i
  support : ∀ j i k, box.outerBox.supportUpper j i k ≤ box.defect j i
  direction_nonzero : ∀ j i,
    box.outerBox.supportUpper j i ((box.outerBox.certificate j).nonzeroWitness i) < 0
  budget : ∀ j, box.outerBox.weightBudget j ≤ (box.outerBox.certificate j).B
  defect_budget : ∀ j, (∑ i, box.outerBox.weightUpper j i * box.defect j i) ≤ box.D j
  variation : ∀ j,
    box.outerBox.variationRadiusSum j + 3 * variationError ≤
      (box.outerBox.certificate j).B * box.outerBox.δ
  barycentric : box.outerBox.barycentricValid
  annular_dominance : ∀ j,
    ((1 / 2) * box.outerBox.r ^ 2 * (box.outerBox.certificate j).B + box.D j) ^ 2 ≤
      box.r0 ^ 2 * (1 - (1 / 4) * box.outerBox.r ^ 2) *
        (box.outerBox.c ^ 2 * (box.outerBox.certificate j).B ^ 2)

instance (box : TwoZoneBox) : Decidable box.Valid :=
  decidable_of_iff _ (TwoZoneBox.valid_iff box).symm

/-- A valid two-zone annular certificate rules out every translated pose in its
atlas interval and signed projective viewing triangle. -/
theorem TwoZoneBox.valid_imp_not_translated_rupert (box : TwoZoneBox) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.innerBox.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.innerBox.root p)
    (hmem : InTriangle (toReal box.innerBox.triangle)
      (AtlasProjectiveView.normalizedView box.innerBox.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.innerBox.chart offset)
      exactPolyhedron.hull := by
  let chart := box.innerBox.chart
  let g := box.innerBox.symmetryIndex
  let relative := relativeRotationAtSymmetry
    (p.matrixPoseWithOffset chart offset) g
  let Q := Noperthedron.SnubCube.so3CLM relative
  let normQ := ‖Q - 1‖
  rcases le_total normQ (box.r0 : ℝ) with h_case1 | h_case2
  · -- Case 1: Inner disk ‖Q - 1‖ ≤ r0. Strict 2D hull contacts rule out the pose.
    apply not_rupertPose_of_projective_local_certificates
      (root := box.innerBox.root) (p := p) (chart := chart) (offset := offset)
      (g := g)
      (edge := fun j i => (box.innerBox.certificate j).exactEdge i)
      (index := fun j i => (box.innerBox.certificate j).index i)
      (B := fun j => ((box.innerBox.certificate j).B : ℝ))
      (c := (box.innerBox.c : ℝ))
    · exact (lt_of_lt_of_le (by norm_num) hscale).ne'
    · intro j
      exact_mod_cast h.inner_valid.B_pos j
    · exact box.innerBox.valid_axis_cover_of_bounds
        h.inner_valid.B_pos h.inner_valid.c_nonneg h.inner_valid.delta_nonneg
        h.inner_valid.variation h.inner_valid.barycentric hscale hmem
    · intro j
      simpa [AxisCertificate.exactWeight, AxisCertificate.supportIndex,
        AxisCertificate.exactSelectedVertex] using
        box.innerBox.valid_budget_of_le h.inner_valid.weight_nonneg
          h.inner_valid.budget hscale hmem j
    · intro a
      apply a.ratio_of_norm_bound (box.innerBox.c : ℝ) (box.r0 : ℝ)
        (by exact_mod_cast h.inner_valid.c_nonneg)
        (by exact_mod_cast h.r0_nonneg)
        h_case1
        (by exact_mod_cast h.inner_angle_bound)
    · exact box.innerBox.valid_direction_nonzero_of_strict
        h.inner_valid.direction_nonzero offset hscale hmem
    · intro j i
      simpa [AxisCertificate.exactWeight] using
        box.innerBox.valid_weight_nonneg_of_lower
          h.inner_valid.weight_nonneg hscale hmem j i
    · intro j
      simpa [AxisCertificate.exactWeight] using
        box.innerBox.valid_weight_pos_of_lower
          h.inner_valid.weight_pos hscale hmem j
    · intro j i k
      have hsup := box.innerBox.valid_support_of_upper (fun _ _ => 0)
        (fun j i k => h.inner_valid.support j i k) offset hscale hmem j i k
      push_cast at hsup
      simpa [AxisCertificate.supportIndex] using hsup
  · -- Case 2: Outer annulus r0 ≤ ‖Q - 1‖ ≤ r. Annular dominance rules out the pose with defect.
    have hscale_outer : 1 ≤ viewScale box.outerBox.root p := by
      rw [h.compatible_root]; exact hscale
    have hmem_outer : InTriangle (toReal box.outerBox.triangle)
        (AtlasProjectiveView.normalizedView box.outerBox.root p) := by
      rw [h.compatible_triangle, h.compatible_root]; exact hmem
    have hp_outer : p ∈ box.outerBox.interval.toReal := by
      rw [h.compatible_interval]; exact hp
    have hchart_eq : p.matrixPoseWithOffset chart offset =
        p.matrixPoseWithOffset box.outerBox.chart offset := by
      rw [h.compatible_chart]
    rw [hchart_eq]
    apply not_rupertPose_of_projective_local_certificates_with_defect
      (root := box.outerBox.root) (p := p) (chart := box.outerBox.chart)
      (offset := offset) (g := box.outerBox.symmetryIndex)
      (edge := fun j i => (box.outerBox.certificate j).exactEdge i)
      (index := fun j i => (box.outerBox.certificate j).index i)
      (defect := fun j i => (box.defect j i : ℝ))
      (B := fun j => ((box.outerBox.certificate j).B : ℝ))
      (D := fun j => (box.D j : ℝ))
      (c := (box.outerBox.c : ℝ))
    · exact (lt_of_lt_of_le (by norm_num) hscale_outer).ne'
    · intro j
      exact_mod_cast h.B_pos j
    · exact box.outerBox.valid_axis_cover_of_bounds
        h.B_pos h.c_nonneg h.delta_nonneg h.variation h.barycentric
        hscale_outer hmem_outer
    · intro j
      simpa [AxisCertificate.exactWeight, AxisCertificate.supportIndex,
        AxisCertificate.exactSelectedVertex] using
        box.outerBox.valid_budget_of_le h.weight_nonneg h.budget
          hscale_outer hmem_outer j
    · intro j
      simpa [AxisCertificate.exactWeight] using
        box.outerBox.valid_defect_budget box.defect box.D
          h.defect_nonneg h.defect_budget hscale_outer hmem_outer j
    · intro a j
      have hmismatch := box.outerBox.valid_mismatch_bound_of_radius
        h.outer_mismatch_bound hp_outer offset
      have hrel_le := norm_relativeRotationAtSymmetry_one_le_inner_mismatch
        (p.matrixPoseWithOffset box.outerBox.chart offset)
        box.outerBox.symmetryIndex
      have hQ_eq : Q = Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.outerBox.chart offset)
            box.outerBox.symmetryIndex) := by
        dsimp [Q, relative]
        rw [hchart_eq, h.compatible_symmetry]
      have hnorm_lower : (box.r0 : ℝ) ≤
          ‖Noperthedron.SnubCube.so3CLM
            (relativeRotationAtSymmetry
              (p.matrixPoseWithOffset box.outerBox.chart offset)
              box.outerBox.symmetryIndex) - 1‖ := by
        rw [← hQ_eq]
        exact h_case2
      have hnorm_upper :
          ‖Noperthedron.SnubCube.so3CLM
            (relativeRotationAtSymmetry
              (p.matrixPoseWithOffset box.outerBox.chart offset)
              box.outerBox.symmetryIndex) - 1‖ ≤ (box.outerBox.r : ℝ) :=
        hrel_le.trans hmismatch
      apply AxisAngle.annular_dominates_of_norm_bounds a
        ((box.outerBox.certificate j).B : ℝ) (box.D j : ℝ) (box.outerBox.c : ℝ)
        (box.r0 : ℝ) (box.outerBox.r : ℝ)
      · exact_mod_cast (h.B_pos j).le
      · exact_mod_cast h.D_nonneg j
      · exact_mod_cast h.c_nonneg
      · exact_mod_cast h.r0_nonneg
      · exact_mod_cast h.outer_r_nonneg
      · exact_mod_cast h.outer_r_le_two
      · exact hnorm_lower
      · exact hnorm_upper
      · have hq := h.annular_dominance j
        have hr : (((1 / 2 : ℚ) * box.outerBox.r ^ 2 * (box.outerBox.certificate j).B + box.D j) ^ 2 : ℝ) ≤
            ((box.r0 ^ 2 * (1 - (1 / 4 : ℚ) * box.outerBox.r ^ 2) *
              (box.outerBox.c ^ 2 * (box.outerBox.certificate j).B ^ 2) : ℚ) : ℝ) := by
          exact_mod_cast hq
        push_cast at hr
        exact hr
    · exact box.outerBox.valid_direction_nonzero_of_strict
        h.direction_nonzero offset hscale_outer hmem_outer
    · intro j i
      simpa [AxisCertificate.exactWeight] using
        box.outerBox.valid_weight_nonneg_of_lower
          h.weight_nonneg hscale_outer hmem_outer j i
    · intro j
      simpa [AxisCertificate.exactWeight] using
        box.outerBox.valid_weight_pos_of_lower
          h.weight_pos hscale_outer hmem_outer j
    · intro j i k
      simpa [AxisCertificate.supportIndex] using
        box.outerBox.valid_support_of_upper box.defect h.support
          offset hscale_outer hmem_outer j i k

/-- No translated Rupert pose exists in the region certified by a valid Two-Zone Box. -/
theorem TwoZoneBox.valid_imp_no_translated_rupert_in_region
    (box : TwoZoneBox) (h : box.Valid) :
    ¬ ∃ p ∈ box.innerBox.interval.toReal, ∃ offset : ℝ²,
      1 ≤ viewScale box.innerBox.root p ∧
      InTriangle (toReal box.innerBox.triangle)
        (AtlasProjectiveView.normalizedView box.innerBox.root p) ∧
      RupertPose (p.matrixPoseWithOffset box.innerBox.chart offset)
        exactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hscale, hmem, hrupert⟩
  exact box.valid_imp_not_translated_rupert h hp offset hscale hmem hrupert

end Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
