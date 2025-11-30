import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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

theorem hull_scalar_prod' {n : ℕ} (V : Finset (E n)) (V_ne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (w : E n) :
    ⟪S, w⟫ ≤ Finset.max' (V.image (⟪·, w⟫)) (by simp [Finset.image_nonempty]; exact V_ne) := by
  sorry

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
def maxH (p : Pose) (poly : Finset ℝ³) (poly_ne : poly.Nonempty) (ε : ℝ) (w : ℝ²) : ℝ :=
  poly.image (H p ε w) |>.max' <| by
    simp only [Finset.image_nonempty]
    exact poly_ne

/--
A compact way of saying "the pose satisfies the global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyehdron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure GlobalTheoremPrecondition (poly : Finset ℝ³) (poly_ne : poly.Nonempty) (p : Pose) (ε : ℝ) : Type where
  S : ℝ³
  S_in_poly : S ∈ poly
  w : ℝ²
  S_unit : ‖(S : ℝ³)‖ = 1
  w_unit : ‖w‖ = 1
  exceeds : G p ε S w > maxH p poly poly_ne ε w

theorem global_theorem (p : Pose) (ε : ℝ) (hε : ε > 0)
    (poly : Finset ℝ³) (poly_ne : poly.Nonempty) (hpoly : polyhedronRadius poly poly_ne = 1)
    (poly_pointsym : PointSym (convexHull ℝ (poly : Set ℝ³)))
    (hp : GlobalTheoremPrecondition poly poly_ne p ε) :
    ¬ ∃ q ∈ p.closed_ball ε, Shadows.IsRupert q (convexHull ℝ poly) := by
  rintro ⟨q, q_near_p, q_is_rupert⟩
  simp only [Membership.mem] at q_near_p

  -- we aim to show max₁ ≥ Sval ≥ G ≥ H ≥ max₂
  let K₁ := poly.image fun P => ⟪p.rotR (p.rotM₁ P), hp.w⟫
  let max₁ := K₁.max' (by simp only [K₁, Finset.image_nonempty]; exact poly_ne)
  let K₂ := poly.image fun P => ⟪(p.rotM₂ P), hp.w⟫
  let max₂ := K₂.max' (by simp only [K₂, Finset.image_nonempty]; exact poly_ne)
  let Sproj := p.rotR (p.rotM₁ hp.S)
  let Sval := ⟪Sproj, hp.w⟫

  let poly_proj := poly.image (fun v => (p.rotM₂ v))
  let poly_proj_ne : poly_proj.Nonempty := by simp only [poly_proj, Finset.image_nonempty]; exact poly_ne
  let Sproj_in_hull : Sproj ∈ convexHull ℝ poly_proj := by sorry

  have : Sval ∈ K₁ :=
    Finset.mem_image_of_mem (fun P ↦ ⟪p.rotR (p.rotM₁ P), hp.w⟫) hp.S_in_poly

  have hgt := by calc
    Sval
    _ ≥ G p ε hp.S hp.w := by sorry
    _ > maxH p poly poly_ne ε hp.w := hp.exceeds
    _ ≥ max₂ := by sorry

  have hle : Sval ≤ max₂ := by
    have h : Sval ≤ _ := hull_scalar_prod' poly_proj poly_proj_ne Sproj Sproj_in_hull hp.w
    simp only [poly_proj, Finset.image_image] at h
    exact h

  exact lt_irrefl _ (lt_of_lt_of_le hgt hle)


theorem global_theorem_nopert (p : Pose) (ε : ℝ) (hε : ε > 0)
    (hp : GlobalTheoremPrecondition nopertVerts nopert_verts_nonempty p ε) :
    ¬ ∃ q ∈ p.closed_ball ε, Shadows.IsRupert q nopert.hull :=
  global_theorem p ε hε nopertVerts nopert_verts_nonempty Nopert.noperthedron_radius_one
      nopert_point_symmetric hp

end GlobalTheorem
