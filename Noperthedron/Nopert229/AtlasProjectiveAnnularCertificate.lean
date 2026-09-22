module

public import Noperthedron.BalancedSupport.FiniteRotation
public import Noperthedron.BalancedSupport.LocalRigidity
public import Noperthedron.BalancedSupport.AxisFree
public import Noperthedron.BalancedSupport.Rodrigues
public import Noperthedron.Nopert229.SymmetryLocal
public import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
public import Noperthedron.Nopert229.AtlasProjectiveLocalRigidity
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Two-Zone Annular Projective Local Certificates

This module implements the two-zone annular certificate method for ruling out
adversary Rupert poses across challenging projective cells on Candidate #229.

In regions where a single 2D hull contact cannot simultaneously certify the
entire spherical zone because an inner contact develops support defect, we split
the domain into two concentric zones around the cell center:
1. Inner core `‖Q - 1‖ ≤ r0`: Certified by a hull support certificate
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
open Matrix
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

/-- Three-way decomposition for a cell:
1. Annular exceptional cone: `r_min ≤ ‖Q - 1‖ ∧ exceptional a.signedAxis`
2. Non-exceptional directions: `¬ exceptional a.signedAxis`
3. Inner exceptional core: `‖Q - 1‖ ≤ r_min ∧ exceptional a.signedAxis`
Together, these three regimes partition the entire rotation ball `‖Q - 1‖ ≤ r`. -/
theorem not_rupertPose_of_three_way_split
    (box : Box)
    (r_min : ℚ)
    (exceptional : ℝ³ → Prop)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (h_annular_cone : ∀ a : AxisAngle
      (Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
      (r_min : ℝ) ≤ ‖Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ →
      exceptional a.signedAxis →
      ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull)
    (h_complement : ∀ a : AxisAngle
      (Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
      ¬ exceptional a.signedAxis →
      ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull)
    (h_inner_core : ∀ a : AxisAngle
      (Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
      ‖Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ ≤ (r_min : ℝ) →
      exceptional a.signedAxis →
      ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  let relative := relativeRotationAtSymmetry
    (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex
  obtain ⟨a⟩ := exists_axisAngle relative.val relative.property
  by_cases hexc : exceptional a.signedAxis
  · by_cases h_inner : ‖Noperthedron.SnubCube.so3CLM relative - 1‖ ≤ (r_min : ℝ)
    · exact h_inner_core a h_inner hexc
    · push_neg at h_inner
      exact h_annular_cone a h_inner.le hexc
  · exact h_complement a hexc

/-- A cell is Rupert-free across its entire viewing triangle and atlas interval
if its adversary rotations are ruled out in:
1. The annular exceptional cone (`h_annular_cone`),
2. The complementary non-exceptional directions (`h_complement`), and
3. The inner exceptional core (`h_inner_core`). -/
theorem valid_imp_not_translated_rupert_of_three_way_split
    (box : Box)
    (r_min : ℚ)
    (exceptional : ℝ³ → Prop)
    (h_annular_cone : ∀ {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
        (r_min : ℝ) ≤ ‖Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ →
        exceptional a.signedAxis →
        ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull)
    (h_complement : ∀ {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
        ¬ exceptional a.signedAxis →
        ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull)
    (h_inner_core : ∀ {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p) →
      ∀ a : AxisAngle
        (Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex)),
        ‖Noperthedron.SnubCube.so3CLM
          (relativeRotationAtSymmetry
            (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ ≤ (r_min : ℝ) →
        exceptional a.signedAxis →
        ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull) :
    ∀ {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²),
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView box.root p) →
      ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  intro p hp offset hscale hmem
  exact not_rupertPose_of_three_way_split box r_min exceptional offset
    (h_annular_cone hp offset hscale hmem)
    (h_complement hp offset hscale hmem)
    (h_inner_core hp offset hscale hmem)

/-- An inner core axis with zero support defect rules out any adversary rotation in the
exceptional cone for small angles ‖Q - 1‖ ≤ r_min. -/
theorem not_rupertPose_of_inner_core_cone_axis
    (box : Box)
    (r_min : ℚ)
    (c_core : ℚ)
    (exceptional : ℝ³ → Prop)
    (hr_min_nonneg : 0 ≤ r_min)
    (hc_core_margin : box.δ ≤ c_core)
    (hB_pos : ∀ j, 0 < (box.certificate j).B)
    (hdelta_nonneg : 0 ≤ box.δ)
    (hvariation : ∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
    (hsupport : ∀ j i k, box.supportUpper j i k ≤ 0)
    (hdir_nonzero : ∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
    (hbudget : ∀ j, box.weightBudget j ≤ (box.certificate j).B)
    (hweight_nonneg : ∀ j i, 0 ≤ box.weightLower j i)
    (hweight_pos : ∀ j, ∃ i, 0 < box.weightLower j i)
    (hexc_covers : ∀ axis, ‖axis‖ = 1 → exceptional axis → (c_core : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0)))
    (hangle_bound : r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2)
    {p : AtlasPose ℝ} (_hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (a : AxisAngle
      ((relativeRotationAtSymmetry
        (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex).val.toEuclideanLin.toContinuousLinearMap))
    (hnorm_upper :
      ‖Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ ≤ (r_min : ℝ))
    (hexc : exceptional a.signedAxis) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  have hc_eff_nonneg : (0 : ℝ) ≤ (c_core : ℝ) - (box.δ : ℝ) := by
    have : (box.δ : ℝ) ≤ (c_core : ℝ) := by exact_mod_cast hc_core_margin
    linarith
  have hB_real_pos : (0 : ℝ) < ((box.certificate 0).B : ℝ) := by exact_mod_cast hB_pos 0
  have hB_real_nonneg : (0 : ℝ) ≤ ((box.certificate 0).B : ℝ) := hB_real_pos.le
  have hangle_ratio : 1 - Real.cos a.angle ≤ |Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ)) := by
    apply AxisAngle.ratio_of_norm_bound a ((c_core : ℝ) - (box.δ : ℝ)) (r_min : ℝ)
      hc_eff_nonneg (by exact_mod_cast hr_min_nonneg) hnorm_upper
    have hr : ((r_min ^ 2 * (1 + (c_core - box.δ) ^ 2)) : ℝ) ≤
        ((4 * (c_core - box.δ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hangle_bound
    push_cast at hr
    exact hr
  have hratio : (1 - Real.cos a.angle) * ((box.certificate 0).B : ℝ) + (0 : ℝ) ≤
      |Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ)) * ((box.certificate 0).B : ℝ) := by
    rw [add_zero]
    calc
      (1 - Real.cos a.angle) * ((box.certificate 0).B : ℝ) ≤
          (|Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ))) * ((box.certificate 0).B : ℝ) :=
        mul_le_mul_of_nonneg_right hangle_ratio hB_real_nonneg
      _ = |Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ)) * ((box.certificate 0).B : ℝ) := by ring
  have hscaleNe := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  have _hmove := box.valid_normalizedVariation_move_of_bounds
    hB_pos hvariation hscale hmem 0
  have ha_norm : ‖a.signedAxis‖ = 1 := a.signedAxis_norm
  have hinner := abs_real_inner_le_norm a.signedAxis
    (normalizedVariation box.root p
      (fun j i => (box.certificate j).exactEdge i)
      (fun j i => (box.certificate j).index i)
      box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) 0 -
        toR3 (box.approxNormalizedCenter 0))
  rw [ha_norm, one_mul, inner_sub_right] at hinner
  have _hcore_dot := hexc_covers a.signedAxis ha_norm hexc
  have _hdeltaReal : (0 : ℝ) ≤ (box.δ : ℝ) := by exact_mod_cast hdelta_nonneg
  rw [abs_le] at hinner
  have _hcone_margin : ((c_core : ℝ) - (box.δ : ℝ)) ≤
      inner ℝ a.signedAxis
        (normalizedVariation box.root p
          (fun j i => (box.certificate j).exactEdge i)
          (fun j i => (box.certificate j).index i)
          box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) 0) := by
    linarith
  apply not_rupertPose_of_symmetry_axisAngle_certificate_with_defect
    (p := p.matrixPoseWithOffset box.chart offset)
    (g := box.symmetryIndex)
    (a := a)
    (index := fun i => (box.certificate 0).index i)
    (weight := fun i => (box.certificate 0).exactWeight box p i)
    (direction := fun i => direction box.root p ((box.certificate 0).exactEdge i))
    (defect := fun _ => 0)
  · exact box.valid_direction_nonzero_of_strict hdir_nonzero offset hscale hmem 0
  · intro i
    simpa [AxisCertificate.exactWeight] using
      box.valid_weight_nonneg_of_lower hweight_nonneg hscale hmem 0 i
  · simpa [AxisCertificate.exactWeight] using
      box.valid_weight_pos_of_lower hweight_pos hscale hmem 0
  · exact weight_balance box.root p (fun i => (box.certificate 0).exactEdge i) hscaleNe
  · intro i k
    have hsup := box.valid_support_of_upper (fun _ _ => 0)
      hsupport offset hscale hmem 0 i k
    push_cast at hsup
    simpa [AxisCertificate.supportIndex] using hsup
  · have hbudget_bound :
        ∑ i, (box.certificate 0).exactWeight box p i *
          (‖direction box.root p ((box.certificate 0).exactEdge i)‖ *
            ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate 0).index i))‖) ≤
          ((box.certificate 0).B : ℝ) := by
      simpa [AxisCertificate.exactWeight, AxisCertificate.supportIndex,
        AxisCertificate.exactSelectedVertex] using
        box.valid_budget_of_le hweight_nonneg hbudget hscale hmem 0
    have hremainder :
        (1 - Real.cos a.angle) *
            (∑ i, (box.certificate 0).exactWeight box p i *
              (‖direction box.root p ((box.certificate 0).exactEdge i)‖ *
                ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate 0).index i))‖)) +
          ∑ i, (box.certificate 0).exactWeight box p i * (0 : ℝ) ≤
          (1 - Real.cos a.angle) * ((box.certificate 0).B : ℝ) := by
      simp only [mul_zero, Finset.sum_const_zero, add_zero]
      exact mul_le_mul_of_nonneg_left hbudget_bound (sub_nonneg.mpr (Real.cos_le_one a.angle))
    have hweight_def : (fun i => (box.certificate 0).exactWeight box p i) =
        weight box.root p (fun i => (box.certificate 0).exactEdge i) := rfl
    rw [Noperthedron.SnubCube.axisAngle_weighted_first_identity a (p.matrixPoseWithOffset box.chart offset)
      (fun i => (box.certificate 0).exactWeight box p i)
      (fun i => direction box.root p ((box.certificate 0).exactEdge i))
      (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate 0).index i)))]
    rw [hweight_def]
    rw [firstVariationVector_eq box.root p box.chart offset (fun i => (box.certificate 0).exactEdge i)
      (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate 0).index i))) hscaleNe]
    have hvar_eq :
        variationVector box.root p (fun i => (box.certificate 0).exactEdge i)
          (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate 0).index i))) =
        ((box.certificate 0).B : ℝ) •
          normalizedVariation box.root p
            (fun j i => (box.certificate j).exactEdge i)
            (fun j i => (box.certificate j).index i)
            box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) 0 := by
      simp only [normalizedVariation, smul_smul]
      rw [mul_inv_cancel₀ (ne_of_gt hB_real_pos), one_smul]
    rw [hvar_eq, real_inner_smul_right]
    have hscaled :
        |Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ)) * ((box.certificate 0).B : ℝ) ≤
          |Real.sin a.angle| * (((box.certificate 0).B : ℝ) *
            inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) 0)) := by
      calc
        |Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ)) * ((box.certificate 0).B : ℝ) =
            |Real.sin a.angle| * (((c_core : ℝ) - (box.δ : ℝ)) * ((box.certificate 0).B : ℝ)) := by ring
        _ ≤ |Real.sin a.angle| * (inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) 0) * ((box.certificate 0).B : ℝ)) := by
          gcongr
        _ = |Real.sin a.angle| * (((box.certificate 0).B : ℝ) *
            inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) 0)) := by ring
    calc
      (1 - Real.cos a.angle) *
          (∑ i, (box.certificate 0).exactWeight box p i *
            (‖direction box.root p ((box.certificate 0).exactEdge i)‖ *
              ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate 0).index i))‖)) +
        ∑ i, (box.certificate 0).exactWeight box p i * (0 : ℝ) ≤
          (1 - Real.cos a.angle) * ((box.certificate 0).B : ℝ) := hremainder
      _ ≤ |Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ)) * ((box.certificate 0).B : ℝ) := by
        calc
          (1 - Real.cos a.angle) * ((box.certificate 0).B : ℝ) ≤
              (|Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ))) * ((box.certificate 0).B : ℝ) :=
            mul_le_mul_of_nonneg_right hangle_ratio hB_real_nonneg
          _ = |Real.sin a.angle| * ((c_core : ℝ) - (box.δ : ℝ)) * ((box.certificate 0).B : ℝ) := by ring
      _ ≤ |Real.sin a.angle| * (((box.certificate 0).B : ℝ) *
            inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) 0)) := hscaled

/-- A single complement axis rules out any adversary rotation whose axis it covers. -/
theorem not_rupertPose_of_single_complement_axis
    (box : Box)
    (j : Fin 4)
    (c_comp : ℚ)
    (hc_comp_margin : box.δ ≤ c_comp)
    (hB_pos : ∀ j, 0 < (box.certificate j).B)
    (hdelta_nonneg : 0 ≤ box.δ)
    (hr_nonneg : 0 ≤ box.r)
    (hmismatch : box.mismatchRadius ≤ box.r)
    (hvariation : ∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
    (hsupport : ∀ i k, box.supportUpper j i k ≤ 0)
    (hdir_nonzero : ∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
    (hbudget : ∀ j, box.weightBudget j ≤ (box.certificate j).B)
    (hweight_nonneg : ∀ j i, 0 ≤ box.weightLower j i)
    (hweight_pos : ∀ j, ∃ i, 0 < box.weightLower j i)
    (hangle_bound : box.r ^ 2 * (1 + (c_comp - box.δ) ^ 2) ≤ 4 * (c_comp - box.δ) ^ 2)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (a : AxisAngle
      ((relativeRotationAtSymmetry
        (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex).val.toEuclideanLin.toContinuousLinearMap))
    (haxis_cover : (c_comp : ℝ) ≤ inner ℝ a.signedAxis (toR3 (box.approxNormalizedCenter j))) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  have hc_eff_nonneg : (0 : ℝ) ≤ (c_comp : ℝ) - (box.δ : ℝ) := by
    have : (box.δ : ℝ) ≤ (c_comp : ℝ) := by exact_mod_cast hc_comp_margin
    linarith
  have hmismatch_bound := box.valid_mismatch_bound_of_radius hmismatch hp offset
  have hrel_le := norm_relativeRotationAtSymmetry_one_le_inner_mismatch
    (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex
  have hnorm_upper :
      ‖Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex) - 1‖ ≤ (box.r : ℝ) :=
    hrel_le.trans hmismatch_bound
  have hB_real_pos : (0 : ℝ) < ((box.certificate j).B : ℝ) := by exact_mod_cast hB_pos j
  have hB_real_nonneg : (0 : ℝ) ≤ ((box.certificate j).B : ℝ) := hB_real_pos.le
  have hangle_ratio : 1 - Real.cos a.angle ≤ |Real.sin a.angle| * ((c_comp : ℝ) - (box.δ : ℝ)) := by
    apply AxisAngle.ratio_of_norm_bound a ((c_comp : ℝ) - (box.δ : ℝ)) (box.r : ℝ)
      hc_eff_nonneg (by exact_mod_cast hr_nonneg) hnorm_upper
    have hr : ((box.r ^ 2 * (1 + (c_comp - box.δ) ^ 2)) : ℝ) ≤
        ((4 * (c_comp - box.δ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hangle_bound
    push_cast at hr
    exact hr
  have hscaleNe := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  have _hmove := box.valid_normalizedVariation_move_of_bounds
    hB_pos hvariation hscale hmem j
  have ha_norm : ‖a.signedAxis‖ = 1 := a.signedAxis_norm
  have hinner := abs_real_inner_le_norm a.signedAxis
    (normalizedVariation box.root p
      (fun j i => (box.certificate j).exactEdge i)
      (fun j i => (box.certificate j).index i)
      box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j -
        toR3 (box.approxNormalizedCenter j))
  rw [ha_norm, one_mul, inner_sub_right] at hinner
  have _hdeltaReal : (0 : ℝ) ≤ (box.δ : ℝ) := by exact_mod_cast hdelta_nonneg
  rw [abs_le] at hinner
  have _hcone_margin : ((c_comp : ℝ) - (box.δ : ℝ)) ≤
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
    (defect := fun _ => 0)
  · exact box.valid_direction_nonzero_of_strict hdir_nonzero offset hscale hmem j
  · intro i
    simpa [AxisCertificate.exactWeight] using
      box.valid_weight_nonneg_of_lower hweight_nonneg hscale hmem j i
  · simpa [AxisCertificate.exactWeight] using
      box.valid_weight_pos_of_lower hweight_pos hscale hmem j
  · exact weight_balance box.root p (fun i => (box.certificate j).exactEdge i) hscaleNe
  · intro i k
    have hsup := box.valid_support_of_upper_single j (fun _ => 0)
      hsupport offset hscale hmem i k
    push_cast at hsup
    simpa [AxisCertificate.supportIndex] using hsup
  · have hbudget_bound :
        ∑ i, (box.certificate j).exactWeight box p i *
          (‖direction box.root p ((box.certificate j).exactEdge i)‖ *
            ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))‖) ≤
          ((box.certificate j).B : ℝ) := by
      simpa [AxisCertificate.exactWeight, AxisCertificate.supportIndex,
        AxisCertificate.exactSelectedVertex] using
        box.valid_budget_of_le hweight_nonneg hbudget hscale hmem j
    have hremainder :
        (1 - Real.cos a.angle) *
            (∑ i, (box.certificate j).exactWeight box p i *
              (‖direction box.root p ((box.certificate j).exactEdge i)‖ *
                ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))‖)) +
          ∑ i, (box.certificate j).exactWeight box p i * (0 : ℝ) ≤
          (1 - Real.cos a.angle) * ((box.certificate j).B : ℝ) := by
      simp only [mul_zero, Finset.sum_const_zero, add_zero]
      exact mul_le_mul_of_nonneg_left hbudget_bound (sub_nonneg.mpr (Real.cos_le_one a.angle))
    have hweight_def : (fun i => (box.certificate j).exactWeight box p i) =
        weight box.root p (fun i => (box.certificate j).exactEdge i) := rfl
    rw [Noperthedron.SnubCube.axisAngle_weighted_first_identity a (p.matrixPoseWithOffset box.chart offset)
      (fun i => (box.certificate j).exactWeight box p i)
      (fun i => direction box.root p ((box.certificate j).exactEdge i))
      (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i)))]
    rw [hweight_def]
    rw [firstVariationVector_eq box.root p box.chart offset (fun i => (box.certificate j).exactEdge i)
      (fun i => exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))) hscaleNe]
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
    have hscaled :
        |Real.sin a.angle| * ((c_comp : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ) ≤
          |Real.sin a.angle| * (((box.certificate j).B : ℝ) *
            inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j)) := by
      calc
        |Real.sin a.angle| * ((c_comp : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ) =
            |Real.sin a.angle| * (((c_comp : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ)) := by ring
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
    calc
      (1 - Real.cos a.angle) *
          (∑ i, (box.certificate j).exactWeight box p i *
            (‖direction box.root p ((box.certificate j).exactEdge i)‖ *
              ‖exactVertex (symmetryAction box.symmetryIndex ((box.certificate j).index i))‖)) +
        ∑ i, (box.certificate j).exactWeight box p i * (0 : ℝ) ≤
          (1 - Real.cos a.angle) * ((box.certificate j).B : ℝ) := hremainder
      _ ≤ |Real.sin a.angle| * ((c_comp : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ) := by
        calc
          (1 - Real.cos a.angle) * ((box.certificate j).B : ℝ) ≤
              (|Real.sin a.angle| * ((c_comp : ℝ) - (box.δ : ℝ))) * ((box.certificate j).B : ℝ) :=
            mul_le_mul_of_nonneg_right hangle_ratio hB_real_nonneg
          _ = |Real.sin a.angle| * ((c_comp : ℝ) - (box.δ : ℝ)) * ((box.certificate j).B : ℝ) := by ring
      _ ≤ |Real.sin a.angle| * (((box.certificate j).B : ℝ) *
            inner ℝ a.signedAxis
              (normalizedVariation box.root p
                (fun j i => (box.certificate j).exactEdge i)
                (fun j i => (box.certificate j).index i)
                box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j)) := hscaled

/-- Core box configuration obtained by replacing certificate with coreAxis. -/
def Box.withCoreAxis (box : Box) (coreAxis : AxisCertificate) (c_core : ℚ) (r_min : ℚ) : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := fun _ => coreAxis
  c := c_core
  δ := box.δ
  r := r_min

theorem bessel_two_poly (u w a : ℝ³) (hortho : inner ℝ u w = (0 : ℝ)) :
    let A := inner ℝ u u
    let B := inner ℝ w w
    let x := inner ℝ a u
    let y := inner ℝ a w
    let p : ℝ³ := (A * B) • a - (B * x) • u - (A * y) • w
    inner ℝ p p = (A * B) * ((A * B) * (inner ℝ a a) - (x^2 * B + y^2 * A)) := by
  intro A B x y p
  have hsym : inner ℝ w u = (0 : ℝ) := by
    rw [real_inner_comm]
    exact hortho
  have hua : inner ℝ u a = inner ℝ a u := real_inner_comm ..
  have hwa : inner ℝ w a = inner ℝ a w := real_inner_comm ..
  dsimp [p]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  dsimp [x, y, A, B]
  rw [hortho, hsym, hua, hwa]
  ring

theorem inner_covers_of_ortho_projection
    (u v : ℝ³) (c1 c2 : ℝ)
    (lam : ℝ) (w : ℝ³)
    (hdecomp : v = lam • u + w)
    (hortho : inner ℝ u w = (0 : ℝ))
    (hu_pos : 0 < inner ℝ u u)
    (hw_pos : 0 < inner ℝ w w)
    (hlam_nonneg : 0 ≤ lam)
    (hc1_nonneg : 0 ≤ c1)
    (hmargin : 0 ≤ lam * c1 - c2)
    (hineq : (inner ℝ w w) * (inner ℝ u u - c1^2) ≤ (inner ℝ u u) * (lam * c1 - c2)^2)
    {a : ℝ³} (ha_norm : ‖a‖ = 1)
    (ha_u : c1 ≤ inner ℝ a u) :
    c2 ≤ inner ℝ a v := by
  let A := inner ℝ u u
  let B := inner ℝ w w
  let x := inner ℝ a u
  let y := inner ℝ a w
  let p : ℝ³ := (A * B) • a - (B * x) • u - (A * y) • w
  have hpoly := bessel_two_poly u w a hortho
  change inner ℝ p p = (A * B) * ((A * B) * (inner ℝ a a) - (x^2 * B + y^2 * A)) at hpoly
  have hp_nonneg : 0 ≤ inner ℝ p p := real_inner_self_nonneg
  rw [hpoly] at hp_nonneg
  have hAB_pos : 0 < A * B := mul_pos hu_pos hw_pos
  have hdiff_nonneg : 0 ≤ (A * B) * (inner ℝ a a) - (x^2 * B + y^2 * A) :=
    nonneg_of_mul_nonneg_right hp_nonneg hAB_pos
  have ha_sq : inner ℝ a a = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, ha_norm, mul_one]
  rw [ha_sq, mul_one] at hdiff_nonneg
  have hle1 : x^2 * B + y^2 * A ≤ A * B := by linarith
  have hle2 : y^2 * A ≤ B * (A - x^2) := by linarith
  have hx_ge : c1 ≤ x := ha_u
  have hB_nonneg : 0 ≤ B := le_of_lt hw_pos
  have hx_sq_ge : c1^2 ≤ x^2 := by
    nlinarith
  have h_diff_le : A - x^2 ≤ A - c1^2 := by linarith
  have h_bound1 : B * (A - x^2) ≤ B * (A - c1^2) := by
    nlinarith
  have h_bound2 : y^2 * A ≤ A * (lam * c1 - c2)^2 := by
    calc y^2 * A ≤ B * (A - x^2) := hle2
      _ ≤ B * (A - c1^2) := h_bound1
      _ ≤ A * (lam * c1 - c2)^2 := hineq
  have hy_sq_le : y^2 ≤ (lam * c1 - c2)^2 := by
    rw [mul_comm] at h_bound2
    exact (mul_le_mul_iff_of_pos_left hu_pos).mp h_bound2
  have hy_abs : |y| ≤ lam * c1 - c2 := by
    rw [sq_le_sq] at hy_sq_le
    rwa [abs_of_nonneg hmargin] at hy_sq_le
  rw [abs_le] at hy_abs
  have hav : inner ℝ a v = lam * x + y := by
    simp [hdecomp, inner_add_right, inner_smul_right, x, y]
  rw [hav]
  have hlam_x : lam * c1 ≤ lam * x := by nlinarith
  linarith

theorem inner_toR3 (u w : Fin 3 → ℚ) :
    inner ℝ (toR3 u) (toR3 w) = ((∑ i, u i * w i : ℚ) : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [toR3, dotProduct]
  simp only [Fin.sum_univ_three]
  have hstar : ∀ x : ℝ, starRingEnd ℝ x = x := fun _ => rfl
  simp only [hstar]
  push_cast
  ring

theorem inner_self_toR3 (u : Fin 3 → ℚ) :
    inner ℝ (toR3 u) (toR3 u) = ((∑ i, (u i)^2 : ℚ) : ℝ) := by
  have := inner_toR3 u u
  simpa [sq] using this

theorem toR3_smul (s : ℚ) (v : Fin 3 → ℚ) :
    toR3 (s • v) = (s : ℝ) • toR3 v := by
  ext i
  dsimp [toR3]
  simp

theorem inner_toR3_smul (a : ℝ³) (s : ℚ) (v : Fin 3 → ℚ) :
    inner ℝ a (toR3 (s • v)) = (s : ℝ) * inner ℝ a (toR3 v) := by
  rw [toR3_smul, real_inner_smul_right]

theorem decomposed_axis_cover_zero (a : ℝ³) (c_cone box_c box_δ : ℚ) (v : Fin 3 → ℚ)
    (hc_cone_pos : 0 < c_cone)
    (hc_sum_pos : 0 < box_c + box_δ)
    (hj_cover : ((box_c + box_δ : ℚ) : ℝ) ≤ inner ℝ a (toR3 (((box_c + box_δ) / c_cone) • v)))
    (hnot_exc : ¬ ((c_cone : ℝ) ≤ inner ℝ a (toR3 v))) : False := by
  rw [inner_toR3_smul] at hj_cover
  have hc_cone_real_pos : 0 < (c_cone : ℝ) := by exact_mod_cast hc_cone_pos
  have hc_sum_real_pos : (0 : ℝ) < (box_c : ℝ) + (box_δ : ℝ) := by exact_mod_cast hc_sum_pos
  push_cast at hj_cover
  rw [div_mul_eq_mul_div, le_div_iff₀ hc_cone_real_pos] at hj_cover
  have h_bound : (c_cone : ℝ) ≤ inner ℝ a (toR3 v) := by
    nlinarith [hj_cover, hc_sum_real_pos]
  exact hnot_exc h_bound

/-- In difficult polyhedra with near-critical projections, narrow slivers in the spherical projection
require decoupling the annular cone aperture `c_cone` from the complement cage inradius `box.c`.
The annular dominance condition on the exceptional axis requires a relatively large cone threshold
`c_cone` (e.g. `c_cone ~ 15/1000`) to dominate the quadratic variation defect, whereas the 3-axis
complement cage caging the remaining sphere may have a smaller geometric inradius `box.c`
(e.g. `box.c ~ 1/10000`). By contracting the exceptional center via the scaling factor
`(box.c + box.δ) / c_cone`, the 4-axis cage simultaneously validates the octahedron inradius and proves
that every unit axis either falls in the exceptional cone (handled by annular dominance and the inner core)
or satisfies the complement margin `box.c`. -/
def Box.decomposedCenter (box : Box) (c_cone : ℚ) (j : Fin 4) : VectorQ :=
  if j = 0 then
    ((box.c + box.δ) / c_cone) • box.approxNormalizedCenter 0
  else
    box.approxNormalizedCenter j

def Box.decomposedBarycentric (box : Box) (c_cone : ℚ) (k : Fin 6) : Fin 4 → ℚ :=
  LocalCertificate.tetraBarycentricQ (box.decomposedCenter c_cone) (box.octahedronTarget k)

def Box.decomposedBarycentricValid (box : Box) (c_cone : ℚ) : Prop :=
  LocalCertificate.tetraDetQ (box.decomposedCenter c_cone) ≠ 0 ∧
    ∀ k j, 0 ≤ box.decomposedBarycentric c_cone k j

instance (box : Box) (c_cone : ℚ) : Decidable (box.decomposedBarycentricValid c_cone) := by
  unfold Box.decomposedBarycentricValid
  infer_instance

theorem Box.decomposedBarycentric_mem_convexHull_of_valid (box : Box) (c_cone : ℚ)
    (hbary : box.decomposedBarycentricValid c_cone) (k : Fin 6) :
    toR3 (box.octahedronTarget k) ∈
      convexHull ℝ {toR3 (box.decomposedCenter c_cone j) | j} := by
  apply Noperthedron.BalancedSupport.mem_convexHull_of_barycentric
    (fun j => toR3 (box.decomposedCenter c_cone j))
    (fun j => (box.decomposedBarycentric c_cone k j : ℝ))
  · intro j
    exact_mod_cast hbary.2 k j
  · exact_mod_cast LocalCertificate.tetraBarycentricQ_sum
      (box.decomposedCenter c_cone) (box.octahedronTarget k)
  · ext coordinate
    have hcoordinate := congrFun
      (LocalCertificate.tetraBarycentricQ_combination
        (box.decomposedCenter c_cone) (box.octahedronTarget k)
        hbary.1) coordinate
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toR3,
      WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp]
    exact_mod_cast hcoordinate

theorem Box.valid_decomposed_center_axis_cover_of_bounds (box : Box) (c_cone : ℚ)
    (hc : 0 ≤ box.c) (hdelta : 0 ≤ box.δ)
    (hbary : box.decomposedBarycentricValid c_cone)
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, ((box.c + box.δ : ℚ) : ℝ) ≤
      inner ℝ axis (toR3 (box.decomposedCenter c_cone j)) := by
  apply Noperthedron.BalancedSupport.octahedral_axis_cover
    (fun j => toR3 (box.decomposedCenter c_cone j))
    ((box.c + box.δ : ℚ) : ℝ)
  · exact_mod_cast add_nonneg hc hdelta
  · have heq : toR3 (box.octahedronTarget 0) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) • xAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_zero]
      ext i; fin_cases i <;> norm_num [xAxis3, toR3]
    rw [← heq]
    exact box.decomposedBarycentric_mem_convexHull_of_valid c_cone hbary 0
  · have heq : toR3 (box.octahedronTarget 1) =
        (-(7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) • xAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_one]
      ext i; fin_cases i <;> norm_num [xAxis3, toR3]
    rw [← heq]
    exact box.decomposedBarycentric_mem_convexHull_of_valid c_cone hbary 1
  · have heq : toR3 (box.octahedronTarget 2) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) • yAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_two]
      ext i; fin_cases i <;> norm_num [yAxis3, toR3]
    rw [← heq]
    exact box.decomposedBarycentric_mem_convexHull_of_valid c_cone hbary 2
  · have heq : toR3 (box.octahedronTarget 3) =
        (-(7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) • yAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_three]
      ext i; fin_cases i <;> norm_num [yAxis3, toR3]
    rw [← heq]
    exact box.decomposedBarycentric_mem_convexHull_of_valid c_cone hbary 3
  · have heq : toR3 (box.octahedronTarget 4) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) • zAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_four]
      ext i; fin_cases i <;> norm_num [zAxis3, toR3]
    rw [← heq]
    exact box.decomposedBarycentric_mem_convexHull_of_valid c_cone hbary 4
  · have heq : toR3 (box.octahedronTarget 5) =
        (-(7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) • zAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_five]
      ext i; fin_cases i <;> norm_num [zAxis3, toR3]
    rw [← heq]
    exact box.decomposedBarycentric_mem_convexHull_of_valid c_cone hbary 5
  · exact haxis

/-- Master theorem for decomposed / annular exceptional-cone certificates.
Combines annular dominance on [r_min, box.r] for Axis 0, complement coverage for
Axes 1..3, and inner core coverage on [0, r_min] for coreAxis to rule out all adversary poses. -/
theorem valid_imp_not_translated_rupert_of_decomposed
    (box : Box)
    (coreAxis : AxisCertificate)
    (defect0 : Fin 3 → ℚ) (D0 : ℚ)
    (r_min : ℚ) (c_cone : ℚ) (c_core : ℚ)
    (hr_min_nonneg : 0 ≤ r_min)
    (hr_nonneg : 0 ≤ box.r)
    (hr_le_two : box.r ≤ 2)
    (hmismatch : box.mismatchRadius ≤ box.r)
    (hdelta_nonneg : 0 ≤ box.δ)
    (hc_nonneg : 0 ≤ box.c)
    (hbary : box.decomposedBarycentricValid c_cone)
    (hD0_nonneg : 0 ≤ D0)
    (hdefect0_nonneg : ∀ i, 0 ≤ defect0 i)
    (hdefect_budget0 : (∑ i, box.weightUpper 0 i * defect0 i) ≤ D0)
    (hc_cone_margin : box.δ ≤ c_cone)
    (hannular_dominance :
      ((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤
        r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) *
          ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2))
    (hB_pos : ∀ j, 0 < (box.certificate j).B)
    (hvar : ∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
    (hsupp : ∀ j i k, box.supportUpper j i k ≤ if j = 0 then defect0 i else 0)
    (hdir_nonzero : ∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
    (hbudget : ∀ j, box.weightBudget j ≤ (box.certificate j).B)
    (hweight_nonneg : ∀ j i, 0 ≤ box.weightLower j i)
    (hweight_pos : ∀ j, ∃ i, 0 < box.weightLower j i)
    (hcomp_angle : box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2)
    (hc_core_margin : box.δ ≤ c_core)
    (hcore_B_pos : 0 < coreAxis.B)
    (hcore_var :
      (box.withCoreAxis coreAxis c_core r_min).variationRadiusSum 0 + 3 * variationError ≤
        coreAxis.B * box.δ)
    (hcore_supp : ∀ i k, (box.withCoreAxis coreAxis c_core r_min).supportUpper 0 i k ≤ 0)
    (hcore_dir : ∀ i,
      (box.withCoreAxis coreAxis c_core r_min).supportUpper 0 i (coreAxis.nonzeroWitness i) < 0)
    (hcore_budget : (box.withCoreAxis coreAxis c_core r_min).weightBudget 0 ≤ coreAxis.B)
    (hcore_weight_nonneg : ∀ i, 0 ≤ (box.withCoreAxis coreAxis c_core r_min).weightLower 0 i)
    (hcore_weight_pos : ∃ i, 0 < (box.withCoreAxis coreAxis c_core r_min).weightLower 0 i)
    (hcore_angle : r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2)
    (hexc_covers : ∀ axis, ‖axis‖ = 1 → (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0)) →
      (c_core : ℝ) ≤ inner ℝ axis (toR3 ((box.withCoreAxis coreAxis c_core r_min).approxNormalizedCenter 0)))
    (hc_cone_pos : 0 < c_cone)
    (hc_margin : box.δ ≤ box.c)
    (hc_sum_pos : 0 < box.c + box.δ)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  let coreBox := box.withCoreAxis coreAxis c_core r_min
  let exceptional : ℝ³ → Prop := fun axis =>
    (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0))
  apply valid_imp_not_translated_rupert_of_three_way_split box r_min exceptional
  · intro p' hp' off' hs' hm' a hnorm_lower hexc
    let fullDefect : Fin 4 → Fin 3 → ℚ := fun j =>
      if j = 0 then defect0 else fun _ => 0
    let fullD : Fin 4 → ℚ := fun j =>
      if j = 0 then D0 else 0
    have hD_nonneg : ∀ j, 0 ≤ fullD j := by
      intro j
      dsimp [fullD]
      split_ifs
      · exact hD0_nonneg
      · exact le_refl 0
    have hdefect_nonneg : ∀ j i, 0 ≤ fullDefect j i := by
      intro j i
      dsimp [fullDefect]
      split_ifs
      · exact hdefect0_nonneg i
      · exact le_refl 0
    have hsupp' : ∀ j i k, box.supportUpper j i k ≤ fullDefect j i := by
      intro j i k
      have hs := hsupp j i k
      dsimp [fullDefect]
      by_cases hj : j = 0
      · subst hj
        simpa using hs
      · simpa [hj] using hs
    have hdefect_budget' : ∀ j, (∑ i, box.weightUpper j i * fullDefect j i) ≤ fullD j := by
      intro j
      dsimp [fullD, fullDefect]
      split_ifs with hj
      · subst hj; exact hdefect_budget0
      · simp
    apply not_rupertPose_of_annular_exceptional_cone_certificate box 0
      fullDefect fullD r_min hr_min_nonneg hr_nonneg hr_le_two
      hB_pos hdelta_nonneg hD_nonneg hdefect_nonneg hvar hsupp' hdir_nonzero
      hbudget hdefect_budget' hweight_nonneg hweight_pos c_cone hc_cone_margin
      exceptional (fun _ => Iff.rfl) hmismatch hannular_dominance hp' off' hs' hm' a
      hnorm_lower hexc
  · intro p' hp' off' hs' hm' a hnot_exc
    have ha_norm : ‖a.signedAxis‖ = 1 := a.signedAxis_norm
    obtain ⟨j, hj_cover⟩ := box.valid_decomposed_center_axis_cover_of_bounds c_cone
      hc_nonneg hdelta_nonneg hbary a.signedAxis ha_norm
    have hdelta_real : (0 : ℝ) ≤ (box.δ : ℝ) := by exact_mod_cast hdelta_nonneg
    have hj_ne_zero : j ≠ 0 := by
      intro hj0
      subst hj0
      apply decomposed_axis_cover_zero a.signedAxis c_cone box.c box.δ (box.approxNormalizedCenter 0)
        hc_cone_pos hc_sum_pos hj_cover hnot_exc
    have hj_supp : ∀ i k, box.supportUpper j i k ≤ 0 := by
      intro i k
      have hs := hsupp j i k
      split_ifs at hs with hj0
      · exact False.elim (hj_ne_zero hj0)
      · exact hs
    have hj_center : toR3 (box.decomposedCenter c_cone j) = toR3 (box.approxNormalizedCenter j) := by
      dsimp [Box.decomposedCenter]
      split_ifs with hj0
      · exact False.elim (hj_ne_zero hj0)
      · rfl
    have hj_cover' : (box.c : ℝ) ≤ inner ℝ a.signedAxis (toR3 (box.approxNormalizedCenter j)) := by
      rw [← hj_center]
      push_cast at hj_cover
      linarith
    apply not_rupertPose_of_single_complement_axis box j box.c
      hc_margin
      hB_pos hdelta_nonneg hr_nonneg hmismatch hvar hj_supp hdir_nonzero
      hbudget hweight_nonneg hweight_pos hcomp_angle hp' off' hs' hm' a hj_cover'
  · intro p' hp' off' hs' hm' a hnorm_upper hexc
    have hexc_core : (c_core : ℝ) ≤ inner ℝ a.signedAxis (toR3 (coreBox.approxNormalizedCenter 0)) :=
      hexc_covers a.signedAxis a.signedAxis_norm hexc
    change ¬ RupertPose (p'.matrixPoseWithOffset coreBox.chart off') exactPolyhedron.hull
    apply not_rupertPose_of_inner_core_cone_axis coreBox r_min c_core exceptional
      hr_min_nonneg hc_core_margin (fun _ => hcore_B_pos) hdelta_nonneg
      (fun _ => hcore_var) (fun _ i k => hcore_supp i k) (fun _ i => hcore_dir i)
      (fun _ => hcore_budget) (fun _ i => hcore_weight_nonneg i) (fun _ => hcore_weight_pos)
      (fun ax ha he => hexc_covers ax ha he) hcore_angle hp' off' hs' hm'
      a hnorm_upper hexc
  · exact hp
  · exact hscale
  · exact hmem

/-- Full decidable verification condition for a decomposed / annular leaf in Lean. -/
@[mk_iff]
structure Box.DecomposedViewValid
    (box : Box) (coreAxis : AxisCertificate)
    (defect0 : Fin 3 → ℚ) (D0 : ℚ)
    (r_min : ℚ) (c_cone : ℚ) (c_core : ℚ)
    (lam : ℚ) (w : Fin 3 → ℚ) : Prop where
  r_min_nonneg : 0 ≤ r_min
  r_nonneg : 0 ≤ box.r
  r_le_two : box.r ≤ 2
  delta_nonneg : 0 ≤ box.δ
  c_nonneg : 0 ≤ box.c
  bary : box.decomposedBarycentricValid c_cone
  D0_nonneg : 0 ≤ D0
  defect0_nonneg : ∀ i, 0 ≤ defect0 i
  defect_budget0 : (∑ i, box.weightUpper 0 i * defect0 i) ≤ D0
  c_cone_margin : box.δ ≤ c_cone
  annular_dominance :
    ((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤
      r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) *
        ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2)
  B_pos : ∀ j, 0 < (box.certificate j).B
  var : ∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ
  supp : ∀ j i k, box.supportUpper j i k ≤ if j = 0 then defect0 i else 0
  dir_nonzero : ∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0
  budget : ∀ j, box.weightBudget j ≤ (box.certificate j).B
  weight_nonneg : ∀ j i, 0 ≤ box.weightLower j i
  weight_pos : ∀ j, ∃ i, 0 < box.weightLower j i
  comp_angle : box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2
  c_core_margin : box.δ ≤ c_core
  core_B_pos : 0 < coreAxis.B
  core_var :
    (box.withCoreAxis coreAxis c_core r_min).variationRadiusSum 0 + 3 * variationError ≤
      coreAxis.B * box.δ
  core_supp : ∀ i k, (box.withCoreAxis coreAxis c_core r_min).supportUpper 0 i k ≤ 0
  core_dir : ∀ i,
    (box.withCoreAxis coreAxis c_core r_min).supportUpper 0 i (coreAxis.nonzeroWitness i) < 0
  core_budget : (box.withCoreAxis coreAxis c_core r_min).weightBudget 0 ≤ coreAxis.B
  core_weight_nonneg : ∀ i, 0 ≤ (box.withCoreAxis coreAxis c_core r_min).weightLower 0 i
  core_weight_pos : ∃ i, 0 < (box.withCoreAxis coreAxis c_core r_min).weightLower 0 i
  core_angle : r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2
  c_cone_pos : 0 < c_cone
  c_margin : box.δ ≤ box.c
  c_sum_pos : 0 < box.c + box.δ
  -- Projection conditions certifying hexc_covers:
  hdecomp : (box.withCoreAxis coreAxis c_core r_min).approxNormalizedCenter 0 =
    lam • box.approxNormalizedCenter 0 + w
  hortho : (∑ i, (box.approxNormalizedCenter 0 i) * (w i)) = 0
  hu_pos : 0 < (∑ i, (box.approxNormalizedCenter 0 i) ^ 2)
  hw_pos : 0 < (∑ i, (w i) ^ 2)
  hlam_nonneg : 0 ≤ lam
  hc_cone_nonneg : 0 ≤ c_cone
  hmargin : 0 ≤ lam * c_cone - c_core
  hineq : (∑ i, (w i) ^ 2) * ((∑ i, (box.approxNormalizedCenter 0 i) ^ 2) - c_cone^2) ≤
    (∑ i, (box.approxNormalizedCenter 0 i) ^ 2) * (lam * c_cone - c_core)^2

instance (box : Box) (coreAxis : AxisCertificate)
    (defect0 : Fin 3 → ℚ) (D0 : ℚ)
    (r_min : ℚ) (c_cone : ℚ) (c_core : ℚ)
    (lam : ℚ) (w : Fin 3 → ℚ) :
    Decidable (box.DecomposedViewValid coreAxis defect0 D0 r_min c_cone c_core lam w) :=
  decidable_of_iff _ (Box.decomposedViewValid_iff box coreAxis defect0 D0 r_min c_cone c_core lam w).symm

theorem Box.valid_imp_not_translated_rupert_of_decomposedViewValid
    (box : Box) (coreAxis : AxisCertificate)
    (defect0 : Fin 3 → ℚ) (D0 : ℚ)
    (r_min : ℚ) (c_cone : ℚ) (c_core : ℚ)
    (lam : ℚ) (w : Fin 3 → ℚ)
    (hview : box.DecomposedViewValid coreAxis defect0 D0 r_min c_cone c_core lam w)
    (hmismatch : box.mismatchRadius ≤ box.r)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) exactPolyhedron.hull := by
  have hu_pos' : (0 : ℝ) < inner ℝ (toR3 (box.approxNormalizedCenter 0)) (toR3 (box.approxNormalizedCenter 0)) := by
    rw [inner_self_toR3]
    exact_mod_cast hview.hu_pos
  have hw_pos' : (0 : ℝ) < inner ℝ (toR3 w) (toR3 w) := by
    rw [inner_self_toR3]
    exact_mod_cast hview.hw_pos
  have hortho' : inner ℝ (toR3 (box.approxNormalizedCenter 0)) (toR3 w) = 0 := by
    rw [inner_toR3]
    exact_mod_cast hview.hortho
  have hdecomp' : toR3 ((box.withCoreAxis coreAxis c_core r_min).approxNormalizedCenter 0) =
      (lam : ℝ) • toR3 (box.approxNormalizedCenter 0) + toR3 w := by
    ext i
    have := congr_fun hview.hdecomp i
    dsimp [toR3]
    exact_mod_cast this
  have hineq' : (inner ℝ (toR3 w) (toR3 w)) * (inner ℝ (toR3 (box.approxNormalizedCenter 0)) (toR3 (box.approxNormalizedCenter 0)) - (c_cone : ℝ)^2) ≤
      (inner ℝ (toR3 (box.approxNormalizedCenter 0)) (toR3 (box.approxNormalizedCenter 0))) * ((lam : ℝ) * (c_cone : ℝ) - (c_core : ℝ))^2 := by
    rw [inner_self_toR3, inner_self_toR3]
    exact_mod_cast hview.hineq
  have hexc_covers : ∀ axis : ℝ³, ‖axis‖ = 1 →
      (c_cone : ℝ) ≤ inner ℝ axis (toR3 (box.approxNormalizedCenter 0)) →
      (c_core : ℝ) ≤ inner ℝ axis (toR3 ((box.withCoreAxis coreAxis c_core r_min).approxNormalizedCenter 0)) := by
    intro axis ha_norm ha_u
    apply inner_covers_of_ortho_projection
      (toR3 (box.approxNormalizedCenter 0))
      (toR3 ((box.withCoreAxis coreAxis c_core r_min).approxNormalizedCenter 0))
      c_cone c_core lam (toR3 w)
      hdecomp' hortho' hu_pos' hw_pos'
      (by exact_mod_cast hview.hlam_nonneg)
      (by exact_mod_cast hview.hc_cone_nonneg)
      (by exact_mod_cast hview.hmargin)
      hineq' ha_norm ha_u
  exact valid_imp_not_translated_rupert_of_decomposed box coreAxis defect0 D0 r_min c_cone c_core
    hview.r_min_nonneg hview.r_nonneg hview.r_le_two hmismatch hview.delta_nonneg hview.c_nonneg
    hview.bary hview.D0_nonneg hview.defect0_nonneg hview.defect_budget0 hview.c_cone_margin
    hview.annular_dominance hview.B_pos hview.var hview.supp hview.dir_nonzero hview.budget
    hview.weight_nonneg hview.weight_pos hview.comp_angle hview.c_core_margin hview.core_B_pos
    hview.core_var hview.core_supp hview.core_dir hview.core_budget hview.core_weight_nonneg
    hview.core_weight_pos hview.core_angle hexc_covers hview.c_cone_pos hview.c_margin hview.c_sum_pos
    hp offset hscale hmem


theorem Box.DecomposedViewValid.retarget {box : Box}
    {coreAxis : AxisCertificate}
    {defect0 : Fin 3 → ℚ} {D0 : ℚ}
    {r_min c_cone c_core lam : ℚ} {w : Fin 3 → ℚ}
    (h : box.DecomposedViewValid coreAxis defect0 D0 r_min c_cone c_core lam w)
    (interval : AtlasInterval ℚ) (chart : CayleyAtlas.ChartIndex) :
    (box.retarget interval chart).DecomposedViewValid coreAxis defect0 D0 r_min c_cone c_core lam w := by
  cases h
  constructor <;> assumption

end Noperthedron.Nopert229.AtlasProjectiveLocalCertificate





