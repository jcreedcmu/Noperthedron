import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.InnerProductSpace.Dual
import Noperthedron.Nopert
import Noperthedron.PoseInterval

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma f_le_max {n : ℕ} {V : Finset (E n)} (w : E n → ℝ) (hw1 : ∀ y ∈ V, 0 ≤ w y)
      (f : E n →ₗ[ℝ] ℝ) :
  ↑(∑ x ∈ V, w x * f x) ≤ ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max := by
  have fx_le_fvmax (x : V) : f x ≤ (Finset.image f V).max := by
    refine Finset.le_max ?_
    simp only [Finset.mem_image]
    exact ⟨x, Finset.coe_mem x, rfl⟩
  push_cast
  refine Finset.sum_le_sum ?_
  intro x hx
  grw [fx_le_fvmax ⟨x, hx⟩]
  exact WithBot.coe_nonneg.mpr (hw1 x hx)

private lemma extract_constant {n : ℕ} {V : Finset (E n)} (w : E n → ℝ)
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max = ↑(∑ x ∈ V, w x) * (Finset.image (⇑f) V).max := by
  let ⟨S', hS'⟩ := convexHull_nonempty_iff.mp ⟨S, hs⟩
  let ⟨m, hm⟩ := Finset.max_of_mem (Finset.mem_image_of_mem f hS')
  rw [hm]
  suffices h : (WithBot.some (∑ x ∈ V, (w x) * m)) = WithBot.some ((∑ x ∈ V, w x) * m) by
    push_cast at h ⊢
    exact h
  refine congrArg WithBot.some ?_
  rw [← Finset.sum_mul]

theorem finset_hull_linear_max {n : ℕ} {V : Finset (E n)}
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ Finset.max (V.image f) := by
  have hs_orig := hs
  rw [Finset.convexHull_eq] at hs
  obtain ⟨w, hw1, hw2, hw3⟩ := hs
  calc
    ↑(f S) = ↑(f (∑ i ∈ V, w i • id i)) := by rw [← hw3, Finset.centerMass_eq_of_sum_1 V id hw2]
    _       = ↑(∑ x ∈ V, w x * f x) := by simp
    _       ≤ ↑(∑ x ∈ V, w x * ((Finset.image f V).max)) := f_le_max w hw1 f
    _       = ↑((∑ x ∈ V, w x) * (Finset.image f V).max) := extract_constant w S hs_orig f
    _       = (Finset.image f V).max := by rw [hw2]; simp

theorem fintype_hull_linear_max {n : ℕ} {ι : Type} [Fintype ι] (V : ι → E n)
    (S : E n) (hs : S ∈ convexHull ℝ (Set.range V)) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ Finset.max (Finset.univ.image (f ∘ V)) := by
  rw [← Finset.image_image]
  exact finset_hull_linear_max S (by simpa) _

theorem hull_scalar_prod {n : ℕ} {ι : Type} [Fintype ι] (V : ι → E n)
    (S : E n) (hs : S ∈ convexHull ℝ (Set.range V)) (w : E n) :
    ⟪w, S⟫ ≤ Finset.max (Finset.univ.image (⟪w, V ·⟫)) :=
  fintype_hull_linear_max V S hs (InnerProductSpace.toDual ℝ (E n) w |>.toLinearMap)

noncomputable
def rotproj_inner (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 0) (x 1) (x 2) S, w⟫

noncomputable
def nth_partial {n : ℕ} (i : Fin n) (f : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

def mixed_partials_bounded {n : ℕ} (f : E n → ℝ) (x : E n) : Prop :=
  ∀ (i j : Fin n), abs ((nth_partial i <| nth_partial j <| f) x) ≤ 1

theorem rotation_partials_bounded (S : ℝ³) (w : ℝ²) (x : ℝ³) :
    mixed_partials_bounded (rotproj_inner S w) x := by
  sorry

theorem bounded_partials_control_difference {n : ℕ} (f : E n → ℝ)
    (fc : ContDiff ℝ 2 f) (x y : E n)
    (ε : ℝ) (hε : ε > 0) (hdiff : (i : Fin n) → |x i - y i| < ε)
    (mpb : mixed_partials_bounded f x) :
    |f x - f y| ≤ ε * ∑ i, |nth_partial i f x| + (n^2 / 2) * ε^2 := by
  let g₀ : ℝ → E n := fun t => (1 - t) • x + t • y
  let g := f ∘ g₀
  let h : ℝ → ℝ  := deriv (fun t => f <| (1 - t) • x + t • y)
  let g' (t : ℝ) : ℝ := ∑ i, (y i - x i) * nth_partial i f ((1 - t) • x + t • y)
  have z : deriv g = g' := by
    ext x
    have hg : DifferentiableAt ℝ f (g₀ x) := by sorry
    have hf : DifferentiableAt ℝ g₀ x := by sorry
    change fderiv ℝ g x 1 = g' x

    simp only [g, fderiv_comp x hg hf,
      ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, one_smul]

    sorry
  let g0 : ℝ → E n := fun t => (1 - t) • x + t • y
  have hg : g = f ∘ g0 := by rfl

  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have hcont : ContinuousOn g (Set.Icc 0 1) := by sorry
  have hderiv : ∀ x ∈ Set.Ioo 0 1, HasDerivAt g (g' x) x := sorry
  have gint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
  sorry

/--
A measure of how far an inner-shadow vertex S can "stick out"
-/
noncomputable
def G (p : Pose) (ε : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.rotR (p.rotM₁ S), w⟫ - ε * |⟪p.rotR' (p.rotM₁ S), w⟫ + ⟪p.rotR (p.rotM₁θ S), w⟫ + ⟪p.rotR (p.rotM₁φ S), w⟫|
  - 9 * ε^2 / 2

/--
A measure of how far an outer-shadow vertex P can "reach" along w.
-/
noncomputable
def H (p : Pose) (ε : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ P, w⟫ + ε * |⟪p.rotM₂θ P, w⟫ + ⟪p.rotM₂φ P, w⟫| + 2 * ε^2

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
noncomputable
def maxH (p : Pose) (ε : ℝ) (w : ℝ²) : ℝ :=
  nopertVerts.image (H p ε w) |>.max' <| by
    simp only [Finset.image_nonempty]; exact
    nopert_verts_nonempty

/--
A compact way of saying "the pose satisfies the global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyehdron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
def global_theorem_precondition (p : Pose) (ε : ℝ) : Prop :=
  ∃ S ∈ nopertVertSet, ∃ (w : ℝ²), G p ε S w > maxH p ε w

theorem global_theorem (p : Pose) (ε : ℝ) (hε : ε > 0)
    (hp : global_theorem_precondition p ε) :
    ¬ ∃ q ∈ p.closed_ball ε, Shadows.IsRupert q nopert.hull := by
  rintro ⟨q, q_near_p, q_is_rupert⟩
  simp only [Membership.mem] at q_near_p
  sorry

end GlobalTheorem
