import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Noperthedron.Nopert
import Noperthedron.PoseInterval

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma f_le_max {n : ℕ} {V : Finset (E n)} (Vne : V.Nonempty) (w : E n → ℝ) (hw1 : ∀ y ∈ V, 0 ≤ w y)
      (f : E n →ₗ[ℝ] ℝ) :
  ↑(∑ x ∈ V, w x * f x) ≤ ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max' (by simp [Finset.image_nonempty]; exact Vne) := by
  have fx_le_fvmax (x : V) : f x ≤ (Finset.image f V).max' (by simp [Finset.image_nonempty]; exact Vne) := by
    refine Finset.le_max' _ _ ?_
    simp only [Finset.mem_image]
    exact ⟨x, Finset.coe_mem x, rfl⟩
  push_cast
  refine Finset.sum_le_sum ?_
  intro x hx
  grw [fx_le_fvmax ⟨x, hx⟩]
  exact hw1 x hx

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

theorem finset_hull_linear_max {n : ℕ} {V : Finset (E n)} (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ (V.image f).max' (by simp [Finset.image_nonempty]; exact Vne) := by
  have Vine : (V.image f).Nonempty := by simp [Finset.image_nonempty]; exact Vne
  have hs_orig := hs
  rw [Finset.convexHull_eq] at hs
  obtain ⟨w, hw1, hw2, hw3⟩ := hs
  calc
    (f S) = (f (∑ i ∈ V, w i • id i)) := by rw [← hw3, Finset.centerMass_eq_of_sum_1 V id hw2]
    _       = ∑ x ∈ V, w x * f x := by simp
    _       ≤ ∑ x ∈ V, w x * ((Finset.image f V).max' Vine) := f_le_max Vne w hw1 f
    _       = (∑ x ∈ V, w x) * ((Finset.image f V).max' Vine) := by rw [← Finset.sum_mul]
    _       = (Finset.image f V).max' (by simp [Finset.image_nonempty]; exact Vne) := by rw [hw2]; simp

theorem hull_scalar_prod {n : ℕ} (V : Finset (E n)) (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (w : E n) :
    ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) (by simp [Finset.image_nonempty]; exact Vne) := by
  exact finset_hull_linear_max Vne S hs (InnerProductSpace.toDual ℝ (E n) w |>.toLinearMap)

noncomputable
def rotproj_inner (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 0) (x 1) (x 2) S, w⟫

noncomputable
def rotproj_inner_unit (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 0) (x 1) (x 2) S, w⟫ / ‖S‖

noncomputable
def nth_partial {n : ℕ} (i : Fin n) (f : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

def mixed_partials_bounded {n : ℕ} (f : E n → ℝ) (x : E n) : Prop :=
  ∀ (i j : Fin n), abs ((nth_partial i <| nth_partial j <| f) x) ≤ 1

theorem rotation_partials_bounded (S : ℝ³) (w : ℝ²) (x : ℝ³) :
    mixed_partials_bounded (rotproj_inner_unit S w) x := by
  sorry

theorem bounded_partials_control_difference {n : ℕ} (f : E n → ℝ)
    (fc : ContDiff ℝ 2 f) (x y : E n)
    (ε : ℝ) (hε : ε > 0) (hdiff : (i : Fin n) → |x i - y i| ≤ ε)
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
  ⟪p.inner S, w⟫ - ε * (|⟪p.rotR' (p.rotM₁ S), w⟫ + ⟪p.rotR (p.rotM₁θ S), w⟫ + ⟪p.rotR (p.rotM₁φ S), w⟫|)
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
def maxH (p : Pose) (poly : GoodPoly) (ε : ℝ) (w : ℝ²) : ℝ :=
  poly.vertices.image (H p ε w) |>.max' <| by
    simp only [Finset.image_nonempty]
    exact poly.nonempty

/--
A compact way of saying "the pose satisfies the global theorem precondition at width ε".
We require the existence of some inner-shadow vertex S from the polyehdron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure GlobalTheoremPrecondition (poly : GoodPoly) (p : Pose) (ε : ℝ) : Type where
  S : ℝ³
  S_in_poly : S ∈ poly.vertices
  w : ℝ²
  w_unit : ‖w‖ = 1
  exceeds : G p ε S w > maxH p poly ε w

noncomputable
def GlobalTheoremPrecondition.Sval
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) (q : Pose) : ℝ:=
    ⟪hp.w, q.inner hp.S⟫

theorem GlobalTheoremPrecondition.norm_S_le_one
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : ‖hp.S‖ ≤ 1 :=
  poly.vertex_radius_le_one hp.S hp.S_in_poly

noncomputable
def imgInner (p : Pose) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.inner P⟫

noncomputable
def maxInner (p : Pose) (poly: GoodPoly) (w : ℝ²) : ℝ :=
  (imgInner p poly.vertices w).max' (by simp only [imgInner, Finset.image_nonempty]; exact poly.nonempty)

noncomputable
def imgOuter (p : Pose) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.outer P⟫

noncomputable
def maxOuter (p : Pose) (poly : GoodPoly) (w : ℝ²) : ℝ :=
  (imgOuter p poly.vertices w).max' (by simp only [imgOuter, Finset.image_nonempty]; exact poly.nonempty)

/--
This is where we use hull_scalar_prod. The text in [SY25] this corresponds to is:

"As noted before, Rupert’s condition and Lemma 18 imply in particular that
max_{P} ⟪ R(α) M(θ₁, φ₁), P, w ⟫ < max_{P} ⟪ M(θ₂, φ₂), P, w ⟫"
-/
theorem global_theorem_le_reasoning (p : Pose)
    (poly : GoodPoly)
    (h_rupert : RupertPose p (convexHull ℝ poly.vertices)) (w : ℝ²) :
    maxInner p poly w ≤ maxOuter p poly w
    := by
  simp only [maxInner]
  refine Finset.max'_le _ _ _ ?_
  intro y hy
  simp only [maxOuter, imgOuter]
  simp only [imgInner, Finset.mem_image] at hy
  obtain ⟨v, ⟨hv, hv'⟩⟩ := hy
  rw [← hv']
  clear hv'
  change ⟪w, p.inner v⟫ ≤ (poly.vertices.image (⟪w, p.outer ·⟫)).max' _
  convert_to ⟪w, p.inner v⟫ ≤ ((poly.vertices.image p.outer).image (⟪w, ·⟫)).max' (by
      simp only [Finset.image_nonempty]; exact poly.nonempty)
  · simp [Finset.image_image]; rfl
  let S := p.inner v
  let V := poly.vertices.image p.outer
  have Vne : V.Nonempty := by simp only [V, Finset.image_nonempty]; exact poly.nonempty
  change ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) _
  refine hull_scalar_prod V Vne S ?_ w
  simp only [Finset.coe_image, V, S]
  exact p.is_rupert_imp_inner_in_outer poly.vertices h_rupert v hv

lemma rotproj_unit_is_c2 {S : ℝ³} (S_nonzero : ‖S‖ > 0) {w : ℝ²} : ContDiff ℝ 2 (rotproj_inner_unit S w) := by
  sorry

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_ii (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (hp : GlobalTheoremPrecondition poly pbar ε) :
    G pbar ε hp.S hp.w ≤ hp.Sval p := by
  let f : ℝ³ → ℝ := rotproj_inner_unit hp.S hp.w
  have S_norm_pos : 0 < ‖hp.S‖ := poly.nontriv hp.S hp.S_in_poly
  have S_norm_le_one : ‖hp.S‖ ≤ 1 := hp.norm_S_le_one
  have hz := bounded_partials_control_difference
    f (rotproj_unit_is_c2 S_norm_pos)
    pbar.innerParams p.innerParams ε hε
    (closed_ball_imp_inner_params_near p_near_pbar)
    (rotation_partials_bounded hp.S hp.w pbar.innerParams)
  simp only [GlobalTheoremPrecondition.Sval, G, tsub_le_iff_right, ge_iff_le]
  simp only [Nat.cast_ofNat] at hz
  have hzs := mul_le_mul_of_nonneg_right hz (ha := le_of_lt S_norm_pos)
  norm_num at hzs
  ring_nf at hzs ⊢
  nth_grw 3 [S_norm_le_one] at hzs
  simp only [one_mul] at hzs
  sorry

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_iv (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (hp : GlobalTheoremPrecondition poly pbar ε) :
    maxOuter p poly hp.w ≤ maxH pbar poly ε hp.w := by
  sorry

/--
Here we run through the "sequence of inequalities [which yield] the desired contradiction"
-/
theorem global_theorem_gt_reasoning (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
     maxInner p poly pc.w > maxOuter p poly pc.w
    := by
  have sval_in_img_inner : pc.Sval p ∈ imgInner p poly.vertices pc.w := by
    simp only [Finset.mem_image, imgInner, GlobalTheoremPrecondition.Sval]
    use pc.S, pc.S_in_poly

  calc
    maxInner p poly pc.w
    _ ≥ pc.Sval p := Finset.le_max' (H2 := sval_in_img_inner)
    _ ≥ G pbar ε pc.S pc.w := global_theorem_inequality_ii pbar p ε hε p_near_pbar poly pc
    _ > maxH pbar poly ε pc.w := pc.exceeds
    _ ≥ maxOuter p poly pc.w := global_theorem_inequality_iv pbar p ε hε p_near_pbar poly pc

/--
The Global Theorem, [SY25] Theorem 17
-/
theorem global_theorem (pbar : Pose) (ε : ℝ) (hε : ε > 0)
    (poly : GoodPoly)
    (_poly_pointsym : PointSym poly.hull)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ¬ ∃ p ∈ pbar.closed_ball ε, RupertPose p poly.hull := by
  rintro ⟨p, p_near_pbar, p_is_rupert⟩
  have hgt := global_theorem_gt_reasoning pbar p ε hε p_near_pbar poly pc
  have hle := global_theorem_le_reasoning p poly p_is_rupert pc.w
  exact lt_irrefl _ (lt_of_lt_of_le hgt hle)

/--
The Global Theorem specialized to the noperthedron.
-/
theorem global_theorem_nopert (pbar : Pose) (ε : ℝ) (hε : ε > 0)
    (pc : GlobalTheoremPrecondition Nopert.poly pbar ε) :
    ¬ ∃ p ∈ pbar.closed_ball ε, RupertPose p nopert.hull :=
  global_theorem pbar ε hε Nopert.poly
      nopert_point_symmetric pc

end GlobalTheorem
