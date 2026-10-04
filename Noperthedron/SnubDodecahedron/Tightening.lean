module

public import Noperthedron.SnubDodecahedron.Symmetry
public import Noperthedron.BalancedSupport.UniversalDomain
public import Noperthedron.BalancedSupport.ViewAntipode

@[expose] public section

/-!
# A symmetry-reduced pose domain

Both azimuths can be reduced modulo `2π/5`.  We retain the shape-independent
bounds for the other three Euler parameters.  The resulting rational box is
the domain that the certificate tree must cover.
-/

namespace Noperthedron.SnubDodecahedron

variable {P : C5Model}

open Real
open Noperthedron.BalancedSupport

noncomputable def tightPoseInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := -4 / 5, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 12 / 5, θ₂ := 8 / 5, φ₁ := 4, φ₂ := 4, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

/-- The rational superset of the closest-representative condition.  Its
width is strictly smaller than one fivefold period, so no symmetry seam is
present inside the domain that the certificate tree must cover. -/
def InTightPoseRegion (q : Pose ℝ) : Prop :=
  q ∈ tightPoseInterval ∧ q.θ₁ - q.θ₂ ∈ Set.Icc (-(2 / 3)) (2 / 3)

/-- The exact angular wedge retained by the fivefold symmetry reduction.
Unlike the rational root box, these sharp bounds preserve the signs of the
first two outer viewing coordinates. -/
def InViewWedge (q : Pose ℝ) : Prop :=
  q.θ₂ ∈ Set.Icc 0 (2 * π / 5) ∧ q.φ₂ ∈ Set.Icc 0 π

private theorem translated_innerShadow_eq (p : Pose ℝ) (offset : ℝ²)
    (S : Set ℝ³) :
    innerShadow (p.matrixPoseWithOffset offset) S =
      (fun x : ℝ² => x + offset) '' (p.inner '' S) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨p.inner v, ⟨v, hv, rfl⟩, ?_⟩
    rw [Noperthedron.BalancedSupport.project_inner_apply,
      matrixPoseWithOffset_inner_rotation_project]
    rfl
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    rw [Noperthedron.BalancedSupport.project_inner_apply,
      matrixPoseWithOffset_inner_rotation_project]
    rfl

private theorem translated_outerShadow_eq (p : Pose ℝ) (offset : ℝ²)
    (S : Set ℝ³) :
    outerShadow (p.matrixPoseWithOffset offset) S = p.outer '' S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (matrixPoseWithOffset_outer_project p offset v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, matrixPoseWithOffset_outer_project p offset v⟩

theorem translated_rupert_iff_of_images {p q : Pose ℝ}
    (offset : ℝ²)
    (hinner : p.inner '' P.polyhedron.hull =
      q.inner '' P.polyhedron.hull)
    (houter : p.outer '' P.polyhedron.hull =
      q.outer '' P.polyhedron.hull) :
    RupertPose (p.matrixPoseWithOffset offset) P.polyhedron.hull ↔
      RupertPose (q.matrixPoseWithOffset offset) P.polyhedron.hull := by
  unfold RupertPose
  rw [translated_innerShadow_eq, translated_innerShadow_eq,
    translated_outerShadow_eq, translated_outerShadow_eq,
    hinner, houter]

/-- Reduce the outer azimuth modulo the exact fivefold symmetry, then choose
the inner representative closest to it.  Thus the only coincident-rotation
stratum in the reduced domain is `θ₁ = θ₂` (rather than an additional seam
at opposite ends of a fundamental interval). -/
theorem tighten_theta (p : Pose ℝ) :
    ∃ q : Pose ℝ,
      q.θ₂ ∈ Set.Ico 0 (2 * π / 5) ∧
      q.θ₁ - q.θ₂ ∈ Set.Ico (-(π / 5)) (π / 5) ∧
      q.φ₁ = p.φ₁ ∧ q.φ₂ = p.φ₂ ∧ q.α = p.α ∧
      p.inner '' P.polyhedron.hull = q.inner '' P.polyhedron.hull ∧
      p.outer '' P.polyhedron.hull = q.outer '' P.polyhedron.hull ∧
      ∃ k : ℤ, q.θ₂ = p.θ₂ + k * (2 * π / 5) := by
  have hperiod : 0 < 2 * π / 5 := div_pos two_pi_pos (by norm_num)
  let θ₂ := Real.emod p.θ₂ (2 * π / 5)
  obtain ⟨k₂, hk₂⟩ :=
    Real.emod_exists_multiple p.θ₂ (2 * π / 5) hperiod
  let d := Real.emod (p.θ₁ - p.θ₂ + π / 5) (2 * π / 5) - π / 5
  let θ₁ := θ₂ + d
  obtain ⟨kd, hkd⟩ := Real.emod_exists_multiple
    (p.θ₁ - p.θ₂ + π / 5) (2 * π / 5) hperiod
  have hd : d ∈ Set.Ico (-(π / 5)) (π / 5) := by
    have h := Real.emod_in_interval
      (a := p.θ₁ - p.θ₂ + π / 5) hperiod
    dsimp [d]
    rcases h with ⟨hl, hu⟩
    constructor <;> linarith
  have hθ₁ : θ₁ = p.θ₁ + (k₂ + kd) * (2 * π / 5) := by
    dsimp [θ₁, θ₂, d]
    rw [hk₂, hkd]
    ring
  let q : Pose ℝ := {p with θ₁ := θ₁, θ₂ := θ₂}
  refine ⟨q, Real.emod_in_interval hperiod, ?_, rfl, rfl, rfl, ?_, ?_, k₂, hk₂⟩
  · simpa [q, θ₁] using hd
  · calc
      p.inner '' P.polyhedron.hull =
          (p.rotR ∘ p.rotM₁) '' P.polyhedron.hull := by
            rw [Pose.inner_eq_RM]
      _ = p.rotR '' (p.rotM₁ '' P.polyhedron.hull) := by
            rw [Set.image_comp]
      _ = p.rotR '' (rotM p.θ₁ p.φ₁ '' P.polyhedron.hull) := rfl
      _ = p.rotR '' (rotM (p.θ₁ + (k₂ + kd) * (2 * π / 5)) p.φ₁ ''
          P.polyhedron.hull) := by
            have hs := rotM_add_fifth_iterated (P := P)
              (θ := p.θ₁) (φ := p.φ₁) (k₂ + kd)
            push_cast at hs
            rw [hs]
      _ = p.rotR '' (rotM θ₁ p.φ₁ '' P.polyhedron.hull) := by rw [hθ₁]
      _ = (q.rotR ∘ q.rotM₁) '' P.polyhedron.hull := by
            rw [Set.image_comp]
            rfl
      _ = q.inner '' P.polyhedron.hull := by rw [Pose.inner_eq_RM]
  · calc
      p.outer '' P.polyhedron.hull =
          p.rotM₂ '' P.polyhedron.hull := by rw [Pose.outer_eq_M]
      _ = rotM p.θ₂ p.φ₂ '' P.polyhedron.hull := rfl
      _ = rotM (p.θ₂ + k₂ * (2 * π / 5)) p.φ₂ ''
          P.polyhedron.hull := by rw [rotM_add_fifth_iterated k₂]
      _ = rotM θ₂ p.φ₂ '' P.polyhedron.hull := by rw [← hk₂]
      _ = q.rotM₂ '' P.polyhedron.hull := rfl
      _ = q.outer '' P.polyhedron.hull := by rw [Pose.outer_eq_M]

private theorem period_lt_root_upper : 2 * π / 5 < (8 / 5 : ℝ) := by
  nlinarith [Real.pi_lt_four]

end Noperthedron.SnubDodecahedron

end
