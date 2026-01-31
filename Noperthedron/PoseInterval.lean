import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic
import Noperthedron.Pose

open scoped Matrix
open scoped Real

/--
Represents a closed 5d box in parameter space.
-/
structure PoseInterval : Type where
  min : Pose
  max : Pose

/--
The 5d box in parameter space that represents what constraints we can
impose on angles merely from general considerations about rotations.
-/
noncomputable
def mediumInterval : PoseInterval where
  min := {
    θ₁ := 0
    θ₂ := 0
    φ₁ := 0
    φ₂ := 0
    α := -π
  }
  max := {
    θ₁ := 2 * π
    θ₂ := 2 * π
    φ₁ := π
    φ₂ := π
    α := π
  }

/--
The 5d box in parameter space that represents what constraints we can
impose on angles taking advantage of the particular symmetries of the
Noperthedron.
-/
noncomputable
def tightInterval : PoseInterval where
  min := {
    θ₁ := 0
    θ₂ := 0
    φ₁ := 0
    φ₂ := 0
    α := -(π / 2)
  }
  max := {
    θ₁ := 2 * π / 15
    θ₂ := 2 * π / 15
    φ₁ := π
    φ₂ := π / 2
    α := π / 2
  }

/--
An interval we need to constrain poses to sometimes for the purposes
of rational approximation reasoning.
-/
noncomputable
def fourInterval : PoseInterval where
  min := {
    θ₁ := -4
    θ₂ := -4
    φ₁ := -4
    φ₂ := -4
    α := -4
  }
  max := {
    θ₁ := 4
    θ₂ := 4
    φ₁ := 4
    φ₂ := 4
    α := 4
  }

namespace Pose

def closed_ball (p : Pose) (ε : ℝ) : PoseInterval := {
  min := {
    θ₁ := p.θ₁ - ε
    θ₂ := p.θ₂ - ε
    φ₁ := p.φ₁ - ε
    φ₂ := p.φ₂ - ε
    α := p.α - ε
  }
  max := {
    θ₁ := p.θ₁ + ε
    θ₂ := p.θ₂ + ε
    φ₁ := p.φ₁ + ε
    φ₂ := p.φ₂ + ε
    α := p.α + ε
  }
}

end Pose

namespace PoseInterval

def contains (iv : PoseInterval) (vp : Pose) : Prop :=
  (vp.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁) ∧
  (vp.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂) ∧
  (vp.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁) ∧
  (vp.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂) ∧
  (vp.α ∈ Set.Icc iv.min.α iv.max.α)

def contains.θ₁Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁ := c.1
def contains.θ₂Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂ := c.2.1
def contains.φ₁Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁ := c.2.2.1
def contains.φ₂Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂ := c.2.2.2.1
def contains.αBound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.α ∈ Set.Icc iv.min.α iv.max.α := c.2.2.2.2

def center (iv : PoseInterval) : Pose where
  θ₁ := (iv.min.θ₁ + iv.max.θ₁)
  θ₂ := (iv.min.θ₂ + iv.max.θ₂)
  φ₁ := (iv.min.φ₁ + iv.max.φ₁)
  φ₂ := (iv.min.φ₂ + iv.max.φ₂)
  α := (iv.min.α + iv.max.α)

end PoseInterval

instance : Membership Pose PoseInterval where
  mem iv vp := iv.contains vp

instance : HasSubset PoseInterval where
  Subset a b := ∀ p, p ∈ a → p ∈ b

structure TightViewPose : Type where
  θ₁ : Set.Icc 0 (2 * π / 15)
  θ₂ : Set.Icc 0 (2 * π / 15)
  φ₁ : Set.Icc 0 π
  φ₂ : Set.Icc 0 (π/2)
  α : Set.Icc (-π/2) (π/2)

noncomputable
instance : PoseLike TightViewPose where
  inner vp := (rotRM vp.θ₁ vp.φ₁ vp.α).toAffineMap
  outer vp := (rotRM vp.θ₂ vp.φ₂ 0).toAffineMap

lemma closed_ball_imp_inner_params_near {p q : Pose} {ε : ℝ}
    (hq : q ∈ p.closed_ball ε) :
    ∀ i, |p.innerParams.ofLp i - q.innerParams.ofLp i| ≤ ε := by
  intro i
  simp [Pose.closed_ball, Membership.mem, PoseInterval.contains] at hq
  obtain ⟨⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩⟩ := hq
  fin_cases i <;> (simp [Pose.innerParams, abs_sub_le_iff]; grind)

lemma mem_closed_ball_abs_sub_α {p q : Pose} {ε : ℝ}
    (hq : p ∈ q.closed_ball ε) : |p.α - q.α| ≤ ε := by
  have := closed_ball_imp_inner_params_near hq 0
  rw [abs_sub_comm] at this
  simpa [Pose.innerParams] using this

lemma mem_closed_ball_abs_sub_θ₁ {p q : Pose} {ε : ℝ}
    (hq : p ∈ q.closed_ball ε) : |p.θ₁ - q.θ₁| ≤ ε := by
  have := closed_ball_imp_inner_params_near hq 1
  rw [abs_sub_comm] at this
  simpa [Pose.innerParams] using this

lemma mem_closed_ball_abs_sub_φ₁ {p q : Pose} {ε : ℝ}
    (hq : p ∈ q.closed_ball ε) : |p.φ₁ - q.φ₁| ≤ ε := by
  have := closed_ball_imp_inner_params_near hq 2
  rw [abs_sub_comm] at this
  simpa [Pose.innerParams] using this

lemma closed_ball_imp_outer_params_near {p q : Pose} {ε : ℝ}
    (hq : q ∈ p.closed_ball ε) :
    ∀ i, |p.outerParams.ofLp i - q.outerParams.ofLp i| ≤ ε := by
  intro i
  simp [Pose.closed_ball, Membership.mem, PoseInterval.contains] at hq
  obtain ⟨_, ⟨_, _⟩, _, ⟨_, _⟩, _⟩ := hq
  fin_cases i <;> (simp [Pose.outerParams, abs_sub_le_iff]; grind)

lemma mem_closed_ball_abs_sub_θ₂ {p q : Pose} {ε : ℝ}
    (hq : p ∈ q.closed_ball ε) : |p.θ₂ - q.θ₂| ≤ ε := by
  have := closed_ball_imp_outer_params_near hq 0
  rw [abs_sub_comm] at this
  simpa [Pose.innerParams] using this

lemma mem_closed_ball_abs_sub_φ₂ {p q : Pose} {ε : ℝ}
    (hq : p ∈ q.closed_ball ε) : |p.φ₂ - q.φ₂| ≤ ε := by
  have := closed_ball_imp_outer_params_near hq 1
  rw [abs_sub_comm] at this
  simpa [Pose.innerParams] using this
