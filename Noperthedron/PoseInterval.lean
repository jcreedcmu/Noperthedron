import Mathlib.Order.Interval.Basic
import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic
import Noperthedron.Pose

open scoped Matrix
open scoped Real

/--
Represents a closed 5d box in parameter space. A `PoseInterval` is a
`NonemptyInterval Pose` (a pair `min ≤ max` of poses, with the order being
componentwise on the five parameters).
-/
@[reducible]
def PoseInterval (R : Type) [PartialOrder R] : Type := NonemptyInterval (Pose R)

namespace PoseInterval

/-- Build a `PoseInterval` from explicit `min`/`max` endpoints together with a
componentwise `min ≤ max` proof. -/
abbrev mk {R : Type} [PartialOrder R] (min max : Pose R) (h : min ≤ max) : PoseInterval R :=
  NonemptyInterval.mk ⟨min, max⟩ h

abbrev min {R : Type} [PartialOrder R] (iv : PoseInterval R) : Pose R := iv.fst
abbrev max {R : Type} [PartialOrder R] (iv : PoseInterval R) : Pose R := iv.snd
abbrev min_le_max {R : Type} [PartialOrder R] (iv : PoseInterval R) : iv.min ≤ iv.max := iv.fst_le_snd

end PoseInterval

/--
The 5d box in parameter space that represents what constraints we can
impose on angles merely from general considerations about rotations.
-/
noncomputable
def mediumInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -π }
    { θ₁ := 2 * π, θ₂ := 2 * π, φ₁ := π, φ₂ := π, α := π }
    (by
      rw [Pose.le_iff]
      have hπ := Real.pi_pos.le
      refine ⟨?_, ?_, hπ, hπ, ?_⟩ <;> linarith [Real.pi_pos])

/--
The 5d box in parameter space that represents what constraints we can
impose on angles taking advantage of the particular symmetries of the
Noperthedron.
-/
noncomputable
def tightInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -(π / 2) }
    { θ₁ := 2 * π / 15, θ₂ := 2 * π / 15, φ₁ := π, φ₂ := π / 2, α := π / 2 }
    (by
      rw [Pose.le_iff]
      have hπ := Real.pi_pos
      refine ⟨?_, ?_, hπ.le, ?_, ?_⟩ <;> linarith)

/--
The `[-4, 4]^5` box, used to constrain poses for rational approximation reasoning.
Polymorphic over the value type so the same name works at both `ℚ` and `ℝ`.
-/
def fourInterval (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] : PoseInterval R :=
  PoseInterval.mk
    { θ₁ := -4, θ₂ := -4, φ₁ := -4, φ₂ := -4, α := -4 }
    { θ₁ := 4, θ₂ := 4, φ₁ := 4, φ₂ := 4, α := 4 }
    (by rw [Pose.le_iff]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num)

@[simp] lemma fourInterval_min {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    (fourInterval R).min = { θ₁ := -4, θ₂ := -4, φ₁ := -4, φ₂ := -4, α := -4 } := rfl

@[simp] lemma fourInterval_max {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    (fourInterval R).max = { θ₁ := 4, θ₂ := 4, φ₁ := 4, φ₂ := 4, α := 4 } := rfl

/-- View a `Pose ℚ` as a `Pose ℝ` by `Rat.cast`-ing each component. -/
def Pose.toReal (p : Pose ℚ) : Pose ℝ where
  θ₁ := (p.θ₁ : ℝ)
  θ₂ := (p.θ₂ : ℝ)
  φ₁ := (p.φ₁ : ℝ)
  φ₂ := (p.φ₂ : ℝ)
  α := (p.α : ℝ)

@[simp] lemma Pose.toReal_θ₁ (p : Pose ℚ) : p.toReal.θ₁ = (p.θ₁ : ℝ) := rfl
@[simp] lemma Pose.toReal_θ₂ (p : Pose ℚ) : p.toReal.θ₂ = (p.θ₂ : ℝ) := rfl
@[simp] lemma Pose.toReal_φ₁ (p : Pose ℚ) : p.toReal.φ₁ = (p.φ₁ : ℝ) := rfl
@[simp] lemma Pose.toReal_φ₂ (p : Pose ℚ) : p.toReal.φ₂ = (p.φ₂ : ℝ) := rfl
@[simp] lemma Pose.toReal_α (p : Pose ℚ) : p.toReal.α = (p.α : ℝ) := rfl

instance {α : Type*} [Preorder α] [DecidableLE α] (p : α) (iv : NonemptyInterval α) :
    Decidable (p ∈ iv) :=
  decidable_of_iff _ NonemptyInterval.mem_def.symm

namespace PoseInterval

/-- `iv.contains p` ↔ `p ∈ Set.Icc iv.min iv.max` ↔ `p ∈ iv`. Provided as a
named alias for legibility at call sites; `iv.contains p` and `p ∈ iv` are
definitionally equal. -/
def contains {R} [PartialOrder R] (iv : PoseInterval R) (vp : Pose R) : Prop := vp ∈ iv

lemma contains_iff_components {R} [PartialOrder R] {iv : PoseInterval R} {p : Pose R} :
    iv.contains p ↔
      (p.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁) ∧
      (p.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂) ∧
      (p.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁) ∧
      (p.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂) ∧
      (p.α ∈ Set.Icc iv.min.α iv.max.α) := by
  simp only [contains, NonemptyInterval.mem_def, Set.mem_Icc, Pose.le_iff]
  grind

def contains.θ₁Bound {R} [PartialOrder R] {iv : PoseInterval R} {p : Pose R} (c : contains iv p) :
    p.θ₁ ∈ Set.Icc iv.min.θ₁ iv.max.θ₁ := (contains_iff_components.mp c).1
def contains.θ₂Bound {R} [PartialOrder R] {iv : PoseInterval R} {p : Pose R} (c : contains iv p) :
    p.θ₂ ∈ Set.Icc iv.min.θ₂ iv.max.θ₂ := (contains_iff_components.mp c).2.1
def contains.φ₁Bound {R} [PartialOrder R] {iv : PoseInterval R} {p : Pose R} (c : contains iv p) :
    p.φ₁ ∈ Set.Icc iv.min.φ₁ iv.max.φ₁ := (contains_iff_components.mp c).2.2.1
def contains.φ₂Bound {R} [PartialOrder R] {iv : PoseInterval R} {p : Pose R} (c : contains iv p) :
    p.φ₂ ∈ Set.Icc iv.min.φ₂ iv.max.φ₂ := (contains_iff_components.mp c).2.2.2.1
def contains.αBound {R} [PartialOrder R] {iv : PoseInterval R} {p : Pose R} (c : contains iv p) :
    p.α ∈ Set.Icc iv.min.α iv.max.α := (contains_iff_components.mp c).2.2.2.2

noncomputable def center {R} [Field R] [PartialOrder R] (iv : PoseInterval R) : Pose R where
  θ₁ := (iv.min.θ₁ + iv.max.θ₁) / 2
  θ₂ := (iv.min.θ₂ + iv.max.θ₂) / 2
  φ₁ := (iv.min.φ₁ + iv.max.φ₁) / 2
  φ₂ := (iv.min.φ₂ + iv.max.φ₂) / 2
  α := (iv.min.α + iv.max.α) / 2

noncomputable def radius {R} [Field R] [LinearOrder R] (iv : PoseInterval R) : R :=
  ((iv.max.θ₁ - iv.min.θ₁) ⊔
   (iv.max.φ₁ - iv.min.φ₁) ⊔
   (iv.max.θ₂ - iv.min.θ₂) ⊔
   (iv.max.φ₂ - iv.min.φ₂) ⊔
   (iv.max.α - iv.min.α)) / 2

end PoseInterval

/-- Bridge the decidable rational membership `p ∈ fourInterval ℚ` to the real form
`(fourInterval ℝ).contains p.toReal`. -/
theorem fourInterval_contains_toReal {p : Pose ℚ}
    (h : p ∈ fourInterval ℚ) : (fourInterval ℝ).contains p.toReal := by
  obtain ⟨hlow, hhigh⟩ := h
  rw [Pose.le_iff] at hlow hhigh
  simp only [fourInterval_min, fourInterval_max] at hlow hhigh
  rw [PoseInterval.contains_iff_components]
  simp only [fourInterval_min, fourInterval_max, Pose.toReal_θ₁, Pose.toReal_θ₂,
             Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α, Set.mem_Icc]
  exact ⟨⟨mod_cast hlow.1,         mod_cast hhigh.1⟩,
         ⟨mod_cast hlow.2.1,       mod_cast hhigh.2.1⟩,
         ⟨mod_cast hlow.2.2.1,     mod_cast hhigh.2.2.1⟩,
         ⟨mod_cast hlow.2.2.2.1,   mod_cast hhigh.2.2.2.1⟩,
         ⟨mod_cast hlow.2.2.2.2,   mod_cast hhigh.2.2.2.2⟩⟩

theorem mem_closed_ball_center_of_mem (iv : PoseInterval ℝ) (p : Pose ℝ) (hp : p ∈ iv) :
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
    (simp only [PoseInterval.center, Real.dist_eq, abs_sub_le_iff]; constructor <;> linarith)

theorem nonempty_closed_ball_radius_nonneg (p q : Pose ℝ) (r : ℝ)
    (hpq : p ∈ Metric.closedBall q r) :
    0 ≤ r := le_trans dist_nonneg hpq

lemma closed_ball_imp_inner_params_near {p q : Pose ℝ} {ε : ℝ}
    (hq : q ∈ Metric.closedBall p ε) :
    ∀ i, |p.innerParams.ofLp i - q.innerParams.ofLp i| ≤ ε := by
  rw [Pose.mem_closedBall_iff] at hq
  obtain ⟨h1, -, h3, -, h5⟩ := hq
  intro i
  simp only [Pose.innerParams, WithLp.ofLp_toLp]
  rw [abs_sub_comm]
  fin_cases i <;> assumption

lemma mem_closed_ball_abs_sub_α {p q : Pose ℝ} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.α - q.α| ≤ ε :=
  ((Pose.mem_closedBall_iff.mp hq).2.2.2.2)

lemma mem_closed_ball_abs_sub_θ₁ {p q : Pose ℝ} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.θ₁ - q.θ₁| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).1

lemma mem_closed_ball_abs_sub_φ₁ {p q : Pose ℝ} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.φ₁ - q.φ₁| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).2.2.1

lemma closed_ball_imp_outer_params_near {p q : Pose ℝ} {ε : ℝ}
    (hq : q ∈ Metric.closedBall p ε) :
    ∀ i, |p.outerParams.ofLp i - q.outerParams.ofLp i| ≤ ε := by
  rw [Pose.mem_closedBall_iff] at hq
  obtain ⟨-, h2, -, h4, -⟩ := hq
  intro i
  simp only [Pose.outerParams, WithLp.ofLp_toLp]
  rw [abs_sub_comm]
  fin_cases i <;> assumption

lemma mem_closed_ball_abs_sub_θ₂ {p q : Pose ℝ} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.θ₂ - q.θ₂| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).2.1

lemma mem_closed_ball_abs_sub_φ₂ {p q : Pose ℝ} {ε : ℝ}
    (hq : p ∈ Metric.closedBall q ε) : |p.φ₂ - q.φ₂| ≤ ε :=
  (Pose.mem_closedBall_iff.mp hq).2.2.2.1
