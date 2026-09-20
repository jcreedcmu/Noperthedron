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

/-- A Decomposed Two-Zone rigidity theorem pairs an outer defect-tolerant annular certificate
with an inner partial axis-cover certificate and an exceptional rotation axis predicate. -/
theorem not_rupertPose_of_decomposed_two_zone
    {J : Type} [Fintype J]
    (outerBox : Box) (h_outer : outerBox.ViewValid)
    (r0 : ℚ) (hr0_nonneg : 0 ≤ r0)
    (defect : Fin 4 → Fin 3 → ℚ) (D : Fin 4 → ℚ)
    (hdefect_nonneg : ∀ j i, 0 ≤ defect j i)
    (hD_nonneg : ∀ j, 0 ≤ D j)
    (houter_support : ∀ j i k, outerBox.supportUpper j i k ≤ defect j i)
    (houter_defect_budget : ∀ j, (∑ i, outerBox.weightUpper j i * defect j i) ≤ D j)
    (hannular_dominance : ∀ j,
      ((1 / 2 : ℚ) * outerBox.r ^ 2 * (outerBox.certificate j).B + D j) ^ 2 ≤
        r0 ^ 2 * (1 - (1 / 4 : ℚ) * outerBox.r ^ 2) *
          (outerBox.c ^ 2 * (outerBox.certificate j).B ^ 2))
    (houter_mismatch_bound : outerBox.mismatchRadius ≤ outerBox.r)
    (houter_r_le_two : outerBox.r ≤ 2)
    (exceptional : ℝ³ → Prop)
    -- Inner partial certificate data
    (inner_c : ℚ) (hinner_c_nonneg : 0 ≤ inner_c)
    (hinner_angle_bound : r0 ^ 2 * (1 + inner_c ^ 2) ≤ 4 * inner_c ^ 2)
    (inner_edge : J → EdgeTriple)
    (inner_index : J → Fin 3 → VertexIndex)
    (inner_B : J → ℚ) (hinner_B_pos : ∀ j, 0 < inner_B j)
    (hinner_direction_nonzero : ∀ (p : AtlasPose ℝ),
      p ∈ outerBox.interval.toReal → 1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle) (AtlasProjectiveView.normalizedView outerBox.root p) →
      ∀ j i, direction outerBox.root p (inner_edge j i) ≠ 0)
    (hinner_weight_nonneg : ∀ (p : AtlasPose ℝ),
      p ∈ outerBox.interval.toReal → 1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle) (AtlasProjectiveView.normalizedView outerBox.root p) →
      ∀ j i, 0 ≤ weight outerBox.root p (inner_edge j) i)
    (hinner_weight_pos : ∀ (p : AtlasPose ℝ),
      p ∈ outerBox.interval.toReal → 1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle) (AtlasProjectiveView.normalizedView outerBox.root p) →
      ∀ j, ∃ i, 0 < weight outerBox.root p (inner_edge j) i)
    (hinner_support : ∀ (p : AtlasPose ℝ) (offset : ℝ²),
      p ∈ outerBox.interval.toReal → 1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle) (AtlasProjectiveView.normalizedView outerBox.root p) →
      ∀ j i k,
        ⟪direction outerBox.root p (inner_edge j i),
            outerProjectionLinear (p.matrixPoseWithOffset outerBox.chart offset)
              (exactVertex k)⟫ ≤
          ⟪direction outerBox.root p (inner_edge j i),
            outerProjectionLinear (p.matrixPoseWithOffset outerBox.chart offset)
              (exactVertex (symmetryAction outerBox.symmetryIndex (inner_index j i)))⟫)
    (hinner_budget : ∀ (p : AtlasPose ℝ),
      p ∈ outerBox.interval.toReal → 1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle) (AtlasProjectiveView.normalizedView outerBox.root p) →
      ∀ j, ∑ i, weight outerBox.root p (inner_edge j) i *
        (‖direction outerBox.root p (inner_edge j i)‖ *
          ‖exactVertex (symmetryAction outerBox.symmetryIndex (inner_index j i))‖) ≤
        (inner_B j : ℝ))
    (hinner_cover : ∀ (p : AtlasPose ℝ),
      p ∈ outerBox.interval.toReal → 1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle) (AtlasProjectiveView.normalizedView outerBox.root p) →
      ∀ axis : ℝ³, ‖axis‖ = 1 →
        (∃ j, (inner_c : ℝ) ≤ ⟪axis,
          normalizedVariation outerBox.root p inner_edge inner_index outerBox.symmetryIndex
            (fun j => (inner_B j : ℝ)) j⟫) ∨
        exceptional axis)
    -- Exceptional obstruction hypothesis on the inner core
    (hexceptional : ∀ (p : AtlasPose ℝ) (hp : p ∈ outerBox.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle) (AtlasProjectiveView.normalizedView outerBox.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset outerBox.chart offset) outerBox.symmetryIndex)),
      ‖Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset outerBox.chart offset) outerBox.symmetryIndex) - 1‖ ≤ (r0 : ℝ) →
      exceptional a.signedAxis →
      ¬ RupertPose (p.matrixPoseWithOffset outerBox.chart offset) exactPolyhedron.hull) :
    ∀ {p : AtlasPose ℝ} (hp : p ∈ outerBox.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale outerBox.root p →
      InTriangle (toReal outerBox.triangle)
        (AtlasProjectiveView.normalizedView outerBox.root p) →
      ¬ RupertPose (p.matrixPoseWithOffset outerBox.chart offset)
        exactPolyhedron.hull := by
  intro p hp offset hscale hmem
  let chart := outerBox.chart
  let g := outerBox.symmetryIndex
  let relative := relativeRotationAtSymmetry
    (p.matrixPoseWithOffset chart offset) g
  let Q := Noperthedron.SnubCube.so3CLM relative
  let normQ := ‖Q - 1‖
  rcases le_total normQ (r0 : ℝ) with h_case1 | h_case2
  · -- Case 1: Inner disk ‖Q - 1‖ ≤ r0. Directional decomposition rules out the pose.
    apply not_rupertPose_of_projective_local_certificates_with_decomposition
      (root := outerBox.root) (p := p) (chart := chart) (offset := offset)
      (g := g) (exceptional := exceptional)
      (edge := inner_edge)
      (index := inner_index)
      (B := fun j => ((inner_B j : ℝ)))
      (c := (inner_c : ℝ))
    · exact (lt_of_lt_of_le (by norm_num) hscale).ne'
    · intro j
      exact_mod_cast hinner_B_pos j
    · exact hinner_cover p hp hscale hmem
    · exact hinner_budget p hp hscale hmem
    · intro a
      apply a.ratio_of_norm_bound (inner_c : ℝ) (r0 : ℝ)
        (by exact_mod_cast hinner_c_nonneg)
        (by exact_mod_cast hr0_nonneg)
        h_case1
        (by exact_mod_cast hinner_angle_bound)
    · exact hinner_direction_nonzero p hp hscale hmem
    · exact hinner_weight_nonneg p hp hscale hmem
    · exact hinner_weight_pos p hp hscale hmem
    · exact hinner_support p offset hp hscale hmem
    · intro a haxis
      exact hexceptional p hp offset hscale hmem a h_case1 haxis
  · -- Case 2: Outer annulus r0 ≤ ‖Q - 1‖ ≤ r. Annular dominance rules out the pose with defect.
    apply not_rupertPose_of_projective_local_certificates_with_defect
      (root := outerBox.root) (p := p) (chart := chart)
      (offset := offset) (g := g)
      (edge := fun j i => (outerBox.certificate j).exactEdge i)
      (index := fun j i => (outerBox.certificate j).index i)
      (defect := fun j i => (defect j i : ℝ))
      (B := fun j => ((outerBox.certificate j).B : ℝ))
      (D := fun j => (D j : ℝ))
      (c := (outerBox.c : ℝ))
    · exact (lt_of_lt_of_le (by norm_num) hscale).ne'
    · intro j
      exact_mod_cast h_outer.B_pos j
    · exact outerBox.valid_axis_cover_of_bounds
        h_outer.B_pos h_outer.c_nonneg h_outer.delta_nonneg h_outer.variation h_outer.barycentric
        hscale hmem
    · intro j
      simpa [AxisCertificate.exactWeight, AxisCertificate.supportIndex,
        AxisCertificate.exactSelectedVertex] using
        outerBox.valid_budget_of_le h_outer.weight_nonneg h_outer.budget
          hscale hmem j
    · intro j
      simpa [AxisCertificate.exactWeight] using
        outerBox.valid_defect_budget defect D
          hdefect_nonneg houter_defect_budget hscale hmem j
    · intro a j
      have hmismatch := outerBox.valid_mismatch_bound_of_radius
        houter_mismatch_bound hp offset
      have hrel_le := norm_relativeRotationAtSymmetry_one_le_inner_mismatch
        (p.matrixPoseWithOffset outerBox.chart offset)
        outerBox.symmetryIndex
      have hnorm_lower : (r0 : ℝ) ≤
          ‖Noperthedron.SnubCube.so3CLM
            (relativeRotationAtSymmetry
              (p.matrixPoseWithOffset outerBox.chart offset)
              outerBox.symmetryIndex) - 1‖ := h_case2
      have hnorm_upper :
          ‖Noperthedron.SnubCube.so3CLM
            (relativeRotationAtSymmetry
              (p.matrixPoseWithOffset outerBox.chart offset)
              outerBox.symmetryIndex) - 1‖ ≤ (outerBox.r : ℝ) :=
        hrel_le.trans hmismatch
      apply AxisAngle.annular_dominates_of_norm_bounds a
        ((outerBox.certificate j).B : ℝ) (D j : ℝ) (outerBox.c : ℝ)
        (r0 : ℝ) (outerBox.r : ℝ)
      · exact_mod_cast (h_outer.B_pos j).le
      · exact_mod_cast hD_nonneg j
      · exact_mod_cast h_outer.c_nonneg
      · exact_mod_cast hr0_nonneg
      · exact_mod_cast h_outer.r_nonneg
      · exact_mod_cast houter_r_le_two
      · exact hnorm_lower
      · exact hnorm_upper
      · have hq := hannular_dominance j
        have hr : (((1 / 2 : ℚ) * outerBox.r ^ 2 * (outerBox.certificate j).B + D j) ^ 2 : ℝ) ≤
            ((r0 ^ 2 * (1 - (1 / 4 : ℚ) * outerBox.r ^ 2) *
              (outerBox.c ^ 2 * (outerBox.certificate j).B ^ 2) : ℚ) : ℝ) := by
          exact_mod_cast hq
        push_cast at hr
        exact hr
    · exact outerBox.valid_direction_nonzero_of_strict
        h_outer.direction_nonzero offset hscale hmem
    · intro j i
      simpa [AxisCertificate.exactWeight] using
        outerBox.valid_weight_nonneg_of_lower
          h_outer.weight_nonneg hscale hmem j i
    · intro j
      simpa [AxisCertificate.exactWeight] using
        outerBox.valid_weight_pos_of_lower
          h_outer.weight_pos hscale hmem j
    · intro j i k
      simpa [AxisCertificate.supportIndex] using
        outerBox.valid_support_of_upper defect houter_support
          offset hscale hmem j i k

/-- A directional certificate for adversary rotations whose signed axis lies in
an exceptional cone centered around the certificate's normalized first variation.
This theorem discharges the `hexceptional` hypothesis in `not_rupertPose_of_decomposed_two_zone`. -/
theorem not_rupertPose_of_exceptional_cone_certificate
    (box : Box)
    (j : Fin 4)
    (defect : Fin 4 → Fin 3 → ℚ) (D : Fin 4 → ℚ)
    (hB_pos : ∀ j, 0 < (box.certificate j).B)
    (hdelta_nonneg : 0 ≤ box.δ)
    (hD_nonneg : ∀ j, 0 ≤ D j)
    (hdefect_nonneg : ∀ j i, 0 ≤ defect j i)
    (hvariation : ∀ j, box.variationRadiusSum j + 3 * variationError ≤
      (box.certificate j).B * box.δ)
    (hsupport : ∀ j i k, box.supportUpper j i k ≤ defect j i)
    (hdir_nonzero : ∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
    (hbudget : ∀ j, box.weightBudget j ≤ (box.certificate j).B)
    (hdefect_budget : ∀ j, (∑ i, box.weightUpper j i * defect j i) ≤ D j)
    (hweight_nonneg : ∀ j i, 0 ≤ box.weightLower j i)
    (hweight_pos : ∀ j, ∃ i, 0 < box.weightLower j i)
    (c_cone : ℚ)
    (exceptional : ℝ³ → Prop)
    (hexc_def : ∀ axis, exceptional axis ↔ (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter j)))
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (a : AxisAngle
      ((relativeRotationAtSymmetry
        (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex).val.toEuclideanLin.toContinuousLinearMap))
    (hexc : exceptional a.signedAxis)
    (hratio : (1 - Real.cos a.angle) * ((box.certificate j).B : ℝ) + (D j : ℝ) ≤
      |Real.sin a.angle| * ((c_cone : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  have hscaleNe := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  have hmove := box.valid_normalizedVariation_move_of_bounds
    hB_pos hvariation hscale hmem j
  have ha_norm : ‖a.signedAxis‖ = 1 := a.signedAxis_norm
  have hinner := abs_real_inner_le_norm a.signedAxis
    (normalizedVariation box.root p
      (fun j i => (box.certificate j).exactEdge i)
      (fun j i => (box.certificate j).index i)
      box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j -
        toR3 (box.approxNormalizedCenter j))
  rw [ha_norm, one_mul, inner_sub_right] at hinner
  rw [hexc_def] at hexc
  have hdeltaReal : (0 : ℝ) ≤ (box.δ : ℝ) := by exact_mod_cast hdelta_nonneg
  rw [abs_le] at hinner
  have hcone_margin : ((c_cone : ℝ) - (box.δ : ℝ)) ≤
      inner ℝ a.signedAxis
        (normalizedVariation box.root p
          (fun j i => (box.certificate j).exactEdge i)
          (fun j i => (box.certificate j).index i)
          box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j) := by
    linarith
  apply not_rupertPose_of_symmetry_axisAngle_certificate_with_defect
    (p := p.matrixPoseWithOffset box.chart offset)
    (g := box.symmetryIndex)
    (a := a)
    (index := fun i => (box.certificate j).index i)
    (weight := fun i => (box.certificate j).exactWeight box p i)
    (direction := fun i => direction box.root p ((box.certificate j).exactEdge i))
    (defect := fun i => (defect j i : ℝ))
  · exact box.valid_direction_nonzero_of_strict hdir_nonzero offset hscale hmem j
  · intro i
    simpa [AxisCertificate.exactWeight] using
      box.valid_weight_nonneg_of_lower hweight_nonneg hscale hmem j i
  · simpa [AxisCertificate.exactWeight] using
      box.valid_weight_pos_of_lower hweight_pos hscale hmem j
  · exact weight_balance box.root p (fun i => (box.certificate j).exactEdge i) hscaleNe
  · intro i k
    simpa [AxisCertificate.supportIndex] using
      box.valid_support_of_upper defect hsupport offset hscale hmem j i k
  · have hbudget_bound :
        ∑ i, (box.certificate j).exactWeight box p i *
          (‖direction box.root p ((box.certificate j).exactEdge i)‖ *
            ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))‖) ≤
          ((box.certificate j).B : ℝ) := by
      simpa [AxisCertificate.exactWeight, AxisCertificate.supportIndex,
        AxisCertificate.exactSelectedVertex] using
        box.valid_budget_of_le hweight_nonneg hbudget hscale hmem j
    have hD_bound :
        ∑ i, (box.certificate j).exactWeight box p i * (defect j i : ℝ) ≤ (D j : ℝ) := by
      simpa [AxisCertificate.exactWeight] using
        box.valid_defect_budget defect D hdefect_nonneg hdefect_budget
          hscale hmem j
    have hremainder :
        (1 - Real.cos a.angle) *
            (∑ i, (box.certificate j).exactWeight box p i *
              (‖direction box.root p ((box.certificate j).exactEdge i)‖ *
                ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))‖)) +
          ∑ i, (box.certificate j).exactWeight box p i * (defect j i : ℝ) ≤
          (1 - Real.cos a.angle) * ((box.certificate j).B : ℝ) + (D j : ℝ) := by
      linarith [mul_le_mul_of_nonneg_left hbudget_bound (sub_nonneg.mpr (Real.cos_le_one a.angle)), hD_bound]
    have hweight_def : (fun i => (box.certificate j).exactWeight box p i) =
        weight box.root p (fun i => (box.certificate j).exactEdge i) := rfl
    rw [Noperthedron.SnubCube.axisAngle_weighted_first_identity a (p.matrixPoseWithOffset box.chart offset)
      (fun i => (box.certificate j).exactWeight box p i)
      (fun i => direction box.root p ((box.certificate j).exactEdge i))
      (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i)))]
    rw [hweight_def]
    rw [firstVariationVector_eq box.root p box.chart offset (fun i => (box.certificate j).exactEdge i)
      (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))) hscaleNe]
    have hB_real_pos : (0 : ℝ) < ((box.certificate j).B : ℝ) := by exact_mod_cast hB_pos j
    have hvar_eq :
        variationVector box.root p (fun i => (box.certificate j).exactEdge i)
          (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))) =
        ((box.certificate j).B : ℝ) •
          normalizedVariation box.root p
            (fun j i => (box.certificate j).exactEdge i)
            (fun j i => (box.certificate j).index i)
            box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j := by
      simp only [normalizedVariation, smul_smul]
      rw [mul_inv_cancel₀ (ne_of_gt hB_real_pos), one_smul]
    rw [hvar_eq, real_inner_smul_right]
    have hsin_nonneg : 0 ≤ |Real.sin a.angle| := abs_nonneg _
    have hscaled :
        |Real.sin a.angle| * ((c_cone : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ) ≤
          |Real.sin a.angle| * (((box.certificate j).B : ℝ) *
            inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j)) := by
      calc
        |Real.sin a.angle| * ((c_cone : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ) =
            |Real.sin a.angle| * (((c_cone : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ)) := by ring
        _ ≤ |Real.sin a.angle| * (inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j) * ((box.certificate j).B : ℝ)) := by
          gcongr
        _ = |Real.sin a.angle| * (((box.certificate j).B : ℝ) *
            inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j)) := by ring
    exact hremainder.trans (hratio.trans hscaled)

/-- Annular variant of `not_rupertPose_of_exceptional_cone_certificate`.
When the adversary rotation norm satisfies `r_min ≤ ‖Q - 1‖ ≤ box.r`, the dominance
inequality is automatically verified by the rational polynomial bound. -/
theorem not_rupertPose_of_annular_exceptional_cone_certificate
    (box : Box)
    (j : Fin 4)
    (defect : Fin 4 → Fin 3 → ℚ) (D : Fin 4 → ℚ)
    (r_min : ℚ)
    (hr_min_nonneg : 0 ≤ r_min)
    (hr_nonneg : 0 ≤ box.r)
    (hr_le_two : box.r ≤ 2)
    (hB_pos : ∀ j, 0 < (box.certificate j).B)
    (hdelta_nonneg : 0 ≤ box.δ)
    (hD_nonneg : ∀ j, 0 ≤ D j)
    (hdefect_nonneg : ∀ j i, 0 ≤ defect j i)
    (hvariation : ∀ j, box.variationRadiusSum j + 3 * variationError ≤
      (box.certificate j).B * box.δ)
    (hsupport : ∀ j i k, box.supportUpper j i k ≤ defect j i)
    (hdir_nonzero : ∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
    (hbudget : ∀ j, box.weightBudget j ≤ (box.certificate j).B)
    (hdefect_budget : ∀ j, (∑ i, box.weightUpper j i * defect j i) ≤ D j)
    (hweight_nonneg : ∀ j i, 0 ≤ box.weightLower j i)
    (hweight_pos : ∀ j, ∃ i, 0 < box.weightLower j i)
    (c_cone : ℚ)
    (hc_cone_margin : box.δ ≤ c_cone)
    (exceptional : ℝ³ → Prop)
    (hexc_def : ∀ axis, exceptional axis ↔ (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter j)))
    (hmismatch : box.mismatchRadius ≤ box.r)
    (hannular_dominance :
      ((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate j).B + D j) ^ 2 ≤
        r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) *
          ((c_cone - box.δ) ^ 2 * (box.certificate j).B ^ 2))
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (a : AxisAngle
      ((relativeRotationAtSymmetry
        (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex).val.toEuclideanLin.toContinuousLinearMap))
    (hnorm_lower : (r_min : ℝ) ≤
      ‖Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖)
    (hexc : exceptional a.signedAxis) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  have hc_eff_nonneg : (0 : ℝ) ≤ (c_cone : ℝ) - (box.δ : ℝ) := by
    have : (box.δ : ℝ) ≤ (c_cone : ℝ) := by exact_mod_cast hc_cone_margin
    linarith
  have hmismatch_bound := box.valid_mismatch_bound_of_radius hmismatch hp offset
  have hrel_le := norm_relativeRotationAtSymmetry_one_le_inner_mismatch
    (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex
  have hnorm_upper :
      ‖Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ ≤ (box.r : ℝ) :=
    hrel_le.trans hmismatch_bound
  have hB_le : 0 ≤ ((box.certificate j).B : ℝ) := by exact_mod_cast (hB_pos j).le
  have hratio := AxisAngle.annular_dominates_of_norm_bounds a
    ((box.certificate j).B : ℝ) (D j : ℝ) ((c_cone : ℝ) - (box.δ : ℝ))
    (r_min : ℝ) (box.r : ℝ)
    hB_le (by exact_mod_cast hD_nonneg j) hc_eff_nonneg
    (by exact_mod_cast hr_min_nonneg) (by exact_mod_cast hr_nonneg)
    (by exact_mod_cast hr_le_two) hnorm_lower hnorm_upper
    (by
      have hr : (((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate j).B + D j) ^ 2 : ℝ) ≤
          ((r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) *
            ((c_cone - box.δ) ^ 2 * (box.certificate j).B ^ 2) : ℚ) : ℝ) := by
        exact_mod_cast hannular_dominance
      push_cast at hr
      exact hr)
  exact not_rupertPose_of_exceptional_cone_certificate box j defect D
    hB_pos hdelta_nonneg hD_nonneg hdefect_nonneg hvariation hsupport hdir_nonzero
    hbudget hdefect_budget hweight_nonneg hweight_pos c_cone exceptional hexc_def
    hp offset hscale hmem a hexc hratio

end Noperthedron.Nopert229.AtlasProjectiveLocalCertificate


