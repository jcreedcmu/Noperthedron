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

namespace PoseInterval

def contains (iv : PoseInterval) (vp : Pose) : Prop := vp ∈ Set.Icc iv.min iv.max

lemma contains_iff_components {iv : PoseInterval} {p : Pose} :
    iv.contains p ↔
      (p.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁) ∧
      (p.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂) ∧
      (p.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁) ∧
      (p.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂) ∧
      (p.α ∈ Set.Icc iv.min.α iv.max.α) := by
  simp only [contains, Set.mem_Icc, Pose.le_iff, Set.mem_Icc]
  grind

def contains.θ₁Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁ := (contains_iff_components.mp c).1
def contains.θ₂Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂ := (contains_iff_components.mp c).2.1
def contains.φ₁Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁ := (contains_iff_components.mp c).2.2.1
def contains.φ₂Bound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂ := (contains_iff_components.mp c).2.2.2.1
def contains.αBound {iv : PoseInterval} {p : Pose} (c : contains iv p) :
    p.α ∈ Set.Icc iv.min.α iv.max.α := (contains_iff_components.mp c).2.2.2.2

noncomputable def center (iv : PoseInterval) : Pose where
  θ₁ := (iv.min.θ₁ + iv.max.θ₁) / 2
  θ₂ := (iv.min.θ₂ + iv.max.θ₂) / 2
  φ₁ := (iv.min.φ₁ + iv.max.φ₁) / 2
  φ₂ := (iv.min.φ₂ + iv.max.φ₂) / 2
  α := (iv.min.α + iv.max.α) / 2

noncomputable def radius (iv : PoseInterval) : ℝ :=
  ((iv.max.θ₁ - iv.min.θ₁) ⊔
   (iv.max.φ₁ - iv.min.φ₁) ⊔
   (iv.max.θ₂ - iv.min.θ₂) ⊔
   (iv.max.φ₂ - iv.min.φ₂) ⊔
   (iv.max.α - iv.min.α)) / 2

end PoseInterval

instance : Membership Pose PoseInterval where
  mem iv vp := iv.contains vp

instance : HasSubset PoseInterval where
  Subset a b := ∀ p, p ∈ a → p ∈ b

theorem mem_closed_ball_center_of_mem (iv : PoseInterval) (p : Pose) (hp : p ∈ iv) :
    p ∈ Metric.closedBall iv.center iv.radius := by
  obtain ⟨⟨h1l, h1h⟩, ⟨h2l, h2h⟩, ⟨h3l, h3h⟩, ⟨h4l, h4h⟩, ⟨h5l, h5h⟩⟩ :=
    PoseInterval.contains_iff_components.mp hp
  simp only [PoseInterval.radius]
  set s := (iv.max.θ₁ - iv.min.θ₁) ⊔ (iv.max.φ₁ - iv.min.φ₁) ⊔
    (iv.max.θ₂ - iv.min.θ₂) ⊔ (iv.max.φ₂ - iv.min.φ₂) ⊔ (iv.max.α - iv.min.α) with hs
  have ha : iv.max.θ₁ - iv.min.θ₁ ≤ s :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hb : iv.max.φ₁ - iv.min.φ₁ ≤ s :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have hc : iv.max.θ₂ - iv.min.θ₂ ≤ s :=
    le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hd : iv.max.φ₂ - iv.min.φ₂ ≤ s := le_sup_of_le_left le_sup_right
  have he : iv.max.α - iv.min.α ≤ s := le_sup_right
  rw [Pose.mem_closedBall_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [PoseInterval.center, abs_sub_le_iff]; constructor <;> linarith)

theorem nonempty_closed_ball_radius_nonneg (p q : Pose) (r : ℝ)
    (hpq : p ∈ Metric.closedBall q r) :
    0 ≤ r := le_trans dist_nonneg hpq

lemma closed_ball_imp_inner_params_near {p q : Pose} {ε : ℝ}
    (hq : q ∈ Metric.closedBall p ε) :
    ∀ i, |p.innerParams.ofLp i - q.innerParams.ofLp i| ≤ ε := by
  rw [Pose.mem_closedBall_iff] at hq
  obtain ⟨h1, -, h3, -, h5⟩ := hq
  intro i
  simp only [Pose.innerParams, WithLp.ofLp_toLp]
  rw [abs_sub_comm]
  fin_cases i <;> assumption

lemma mem_closed_ball_abs_sub_α {p q : Pose} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.α - q.α| ≤ ε :=
  ((Pose.mem_closedBall_iff.mp hq).2.2.2.2)

lemma mem_closed_ball_abs_sub_θ₁ {p q : Pose} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.θ₁ - q.θ₁| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).1

lemma mem_closed_ball_abs_sub_φ₁ {p q : Pose} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.φ₁ - q.φ₁| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).2.2.1

lemma closed_ball_imp_outer_params_near {p q : Pose} {ε : ℝ}
    (hq : q ∈ Metric.closedBall p ε) :
    ∀ i, |p.outerParams.ofLp i - q.outerParams.ofLp i| ≤ ε := by
  rw [Pose.mem_closedBall_iff] at hq
  obtain ⟨-, h2, -, h4, -⟩ := hq
  intro i
  simp only [Pose.outerParams, WithLp.ofLp_toLp]
  rw [abs_sub_comm]
  fin_cases i <;> assumption

lemma mem_closed_ball_abs_sub_θ₂ {p q : Pose} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.θ₂ - q.θ₂| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).2.1

lemma mem_closed_ball_abs_sub_φ₂ {p q : Pose} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.φ₂ - q.φ₂| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).2.2.2.1
