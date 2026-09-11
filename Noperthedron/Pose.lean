module

public import Noperthedron.PoseClasses
public import Noperthedron.Basic

@[expose] public section


structure Pose (R : Type) : Type where
  θ₁ : R
  θ₂ : R
  φ₁ : R
  φ₂ : R
  α : R
deriving DecidableEq, Repr

instance {R : Type} [ToString R] : ToString (Pose R) where
  toString p := s!"\{θ₁ := {p.θ₁}, θ₂ := {p.θ₂}, φ₁ := {p.φ₁}, φ₂ := {p.φ₂}, α := {p.α}}"

namespace Pose

/-- Bijection between `Pose` and `Fin 5 → ℝ`, used to transfer
the (sup-norm) `MetricSpace` instance from the Pi type. -/
def equivPi {R : Type} : Pose R ≃ (Fin 5 → R) where
  toFun p := ![p.θ₁, p.θ₂, p.φ₁, p.φ₂, p.α]
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4⟩
  left_inv p := by cases p; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

/-- Sup-norm transferred from `Fin 5 → R`. -/
instance {R} [MetricSpace R] : MetricSpace (Pose R) :=
  MetricSpace.induced equivPi equivPi.injective inferInstance

instance {R} [PartialOrder R] : PartialOrder (Pose R) := PartialOrder.lift equivPi equivPi.injective

lemma le_iff {R} [PartialOrder R] (p q : Pose R) :
    p ≤ q ↔ p.θ₁ ≤ q.θ₁ ∧ p.θ₂ ≤ q.θ₂ ∧ p.φ₁ ≤ q.φ₁ ∧ p.φ₂ ≤ q.φ₂ ∧ p.α ≤ q.α := by
  show equivPi p ≤ equivPi q ↔ _
  rw [Pi.le_def]
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩, ?_⟩
  rintro ⟨h1, h2, h3, h4, h5⟩ i
  fin_cases i <;> assumption

instance {R} [PartialOrder R] [DecidableLE R] : DecidableLE (Pose R) :=
  fun p q => decidable_of_iff _ (le_iff p q).symm

lemma mem_closedBall_iff {R} [MetricSpace R] {p q : Pose R} {ε : ℝ} :
    p ∈ Metric.closedBall q ε ↔
      dist p.θ₁ q.θ₁ ≤ ε ∧ dist p.θ₂ q.θ₂ ≤ ε ∧
      dist p.φ₁ q.φ₁ ≤ ε ∧ dist p.φ₂ q.φ₂ ≤ ε ∧ dist p.α q.α ≤ ε := by
  rw [Metric.mem_closedBall,
      show dist p q = dist (equivPi p) (equivPi q) from rfl,
      dist_pi_le_iff']
  refine ⟨fun h => ?_, ?_⟩
  · exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩ i
    fin_cases i <;> assumption

end Pose

namespace Pose

-- Some convenience functions for doing rotations with dot notation
-- Maybe the rotations in basic could be inlined here? It depends on whether
-- we actually use them not in the context of a Pose.

noncomputable
def rotM₁ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₁) (p.φ₁)
noncomputable
def rotM₂ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₂) (p.φ₂)
noncomputable
def rotR (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.rotR (p.α)
noncomputable
def vecX₁ (p : Pose ℝ) : ℝ³ := vecX (p.θ₁) (p.φ₁)
noncomputable
def vecX₂ (p : Pose ℝ) : ℝ³ := vecX (p.θ₂) (p.φ₂)

noncomputable
def rotM₁θ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₁φ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂φ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₂) (p.φ₂)
noncomputable
def rotR' (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.rotR' (p.α)

noncomputable
def rotM₁θθ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₁θφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₁φφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θθ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₂θφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθφ (p.θ₂) (p.φ₂)
noncomputable
def rotM₂φφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφφ (p.θ₂) (p.φ₂)

/-- The inner projection `R(α) M(θ₁, φ₁)` of [SY25] (5) and the outer projection
`M(θ₂, φ₂)`, as the `PoseLike` structure of a real pose. -/
noncomputable
instance : PoseLike (Pose ℝ) where
  inner p := (p.rotR ∘L p.rotM₁).toAffineMap
  outer p := p.rotM₂.toAffineMap

noncomputable
abbrev inner (p : Pose ℝ) : ℝ³ →ᵃ[ℝ] ℝ² := PoseLike.inner p
noncomputable
abbrev outer (p : Pose ℝ) : ℝ³ →ᵃ[ℝ] ℝ² := PoseLike.outer p

def innerParams (p : Pose ℝ) : ℝ³ := !₂[p.α, p.θ₁, p.φ₁]

def outerParams (p : Pose ℝ) : ℝ² := !₂[p.θ₂, p.φ₂]

lemma inner_eq_RM (p : Pose ℝ) : ⇑p.inner = p.rotR ∘ p.rotM₁ := rfl

lemma outer_eq_M (p : Pose ℝ) : ⇑p.outer = ⇑p.rotM₂ := rfl

lemma inner_shadow_eq_img_inner (p : Pose ℝ) (S : Set ℝ³) :
    innerShadow p S = p.inner '' S := rfl

lemma outer_shadow_eq_img_outer (p : Pose ℝ) (S : Set ℝ³) :
    outerShadow p S = p.outer '' S := rfl

lemma inner_shadow_eq_RM (p : Pose ℝ) (S : Set ℝ³) :
    innerShadow p S = (p.rotR ∘L p.rotM₁) '' S := rfl

lemma outer_shadow_eq_M (p : Pose ℝ) (S : Set ℝ³) :
    outerShadow p S = p.rotM₂ '' S := rfl

/--
If we have a convex polyhedron with p being a pose witness of the
rupert property, then in particular every vertex in the "inner"
transformation lies in the convex hull of the vertices under the
"outer" transformation.
-/
theorem is_rupert_imp_inner_in_outer (p : Pose ℝ)
    (poly : Finset ℝ³)
    (h_rupert : RupertPose p (convexHull ℝ poly)) (v : ℝ³) (hv : v ∈ poly) :
     p.inner v ∈ convexHull ℝ (p.outer '' poly) := by
  simp only [RupertPose] at h_rupert
  grw [← subset_closure, interior_subset] at h_rupert
  rw [← AffineMap.image_convexHull p.outer poly]
  exact h_rupert (Set.mem_image_of_mem _ (subset_convexHull ℝ _ hv))

end Pose

end
