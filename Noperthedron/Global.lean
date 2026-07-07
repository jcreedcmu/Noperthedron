import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Noperthedron.PoseInterval
import Noperthedron.Global.Basic
import Noperthedron.Global.BoundedPartialsControlDifference
import Noperthedron.Global.RotationPartials
import Noperthedron.Vertices.Exact

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
    f S ≤ (V.image f).max' (Finset.image_nonempty.mpr Vne) := by
  have Vine : (V.image f).Nonempty := by simp [Finset.image_nonempty]; exact Vne
  have hs_orig := hs
  rw [Finset.convexHull_eq] at hs
  obtain ⟨w, hw1, hw2, hw3⟩ := hs
  calc
    (f S) = (f (∑ i ∈ V, w i • id i)) := by rw [← hw3, Finset.centerMass_eq_of_sum_1 V id hw2]
    _       = ∑ x ∈ V, w x * f x := by simp
    _       ≤ ∑ x ∈ V, w x * ((Finset.image f V).max' Vine) := f_le_max Vne w hw1 f
    _       = (∑ x ∈ V, w x) * ((Finset.image f V).max' Vine) := by rw [← Finset.sum_mul]
    _       = (Finset.image f V).max' _ := by rw [hw2]; simp

/- [SY25] Lemma 18 -/
theorem hull_scalar_prod {n : ℕ} (V : Finset (E n)) (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (w : E n) :
    ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) (Finset.image_nonempty.mpr Vne) := by
  exact finset_hull_linear_max Vne S hs (InnerProductSpace.toDual ℝ (E n) w |>.toLinearMap)

-- rotproj_inner, rotproj_inner_unit, rotproj_outer_unit, rotation_partials_exist,
-- rotation_partials_exist_outer are now imported from Noperthedron.Global.Definitions
-- (via Noperthedron.Global.RotationPartials)

-- rotation_partials_bounded, rotation_partials_bounded_outer ([SY25] Lemma 19) are now
-- imported from Noperthedron.Global.RotationPartials (via SecondPartialInner/SecondPartialOuter)

/--
A measure of how far an inner-shadow vertex S can "stick out".

Second-order version: the ε-penalty carries the first partials, the exact
second partials at the center (weighted by multiplicity from the symmetric
3×3 table), and a `(3³/6)·ε³ = 9ε³/2` Lagrange remainder from the bounded
third partials.  [SY25] uses the weaker first-order penalty `9ε²/2`.
-/
noncomputable
def G (p : Pose ℝ) (ε : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.inner S, w⟫ - (ε * (|⟪p.rotR' (p.rotM₁ S), w⟫| + |⟪p.rotR (p.rotM₁θ S), w⟫| + |⟪p.rotR (p.rotM₁φ S), w⟫|)
  + ε^2 / 2 * (|⟪p.rotR (p.rotM₁ S), w⟫|
      + 2 * |⟪p.rotR' (p.rotM₁θ S), w⟫| + 2 * |⟪p.rotR' (p.rotM₁φ S), w⟫|
      + |⟪p.rotR (p.rotM₁θθ S), w⟫| + 2 * |⟪p.rotR (p.rotM₁θφ S), w⟫|
      + |⟪p.rotR (p.rotM₁φφ S), w⟫|)
  + 9 * ε^3 / 2)

/--
A measure of how far an outer-shadow vertex P can "reach" along w.

Second-order version; the Lagrange remainder is `(2³/6)·ε³ = 4ε³/3`.
-/
noncomputable
def H (p : Pose ℝ) (ε : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ P, w⟫ + ε * (|⟪p.rotM₂θ P, w⟫| + |⟪p.rotM₂φ P, w⟫|)
  + ε^2 / 2 * (|⟪p.rotM₂θθ P, w⟫| + 2 * |⟪p.rotM₂θφ P, w⟫| + |⟪p.rotM₂φφ P, w⟫|)
  + 4 * ε^3 / 3

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
noncomputable
def maxH {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℝ) (poly : GoodPoly ι) (ε : ℝ) (w : ℝ²) : ℝ :=
  Finset.image (H p ε w ∘ poly.vertices.v) Finset.univ |>.max' <| by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr ne

/--
A compact way of saying "the pose satisfies the global theorem precondition at width ε".
We require the index `Si` of some inner-shadow vertex of the polyhedron, and a covector w meant
to express the direction we're projecting ℝ² → ℝ to find that the vertex "sticks out too far"
compared to all the other outer-shadow vertices P (which the calculation of H iterates over)
in the polygon that lies in ℝ².
-/
structure GlobalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p : Pose ℝ) (ε : ℝ) : Type where
  Si : ι
  w : ℝ²
  w_unit : ‖w‖ = 1
  exceeds : G p ε (poly.vertices.v Si) w > maxH p poly ε w

/-- The inner-shadow vertex singled out by the precondition. -/
noncomputable
def GlobalTheoremPrecondition.S
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : ℝ³ :=
  poly.vertices.v hp.Si

noncomputable
def GlobalTheoremPrecondition.Sval
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) (q : Pose ℝ) : ℝ :=
    ⟪hp.w, q.inner hp.S⟫

theorem GlobalTheoremPrecondition.norm_S_le_one
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : ‖hp.S‖ ≤ 1 :=
  poly.vertex_radius_le_one hp.Si

theorem GlobalTheoremPrecondition.norm_S_gt_zero
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : 0 < ‖hp.S‖ :=
  poly.nontriv hp.Si

theorem GlobalTheoremPrecondition.norm_S_ne_zero
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : 0 ≠ ‖hp.S‖ :=
  ne_of_lt hp.norm_S_gt_zero

noncomputable
def imgInner (p : Pose ℝ) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.inner P⟫

noncomputable
def maxInner {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℝ) (poly : GoodPoly ι) (w : ℝ²) : ℝ :=
  (imgInner p (Finset.image poly.vertices.v Finset.univ) w).max' (by
    simp only [imgInner, Finset.image_nonempty, Finset.univ_nonempty_iff]; exact ne)

noncomputable
def imgOuter (p : Pose ℝ) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.outer P⟫

noncomputable
def maxOuter {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℝ) (poly : GoodPoly ι) (w : ℝ²) : ℝ :=
  (imgOuter p (Finset.image poly.vertices.v Finset.univ) w).max' (by
    simp only [imgOuter, Finset.image_nonempty, Finset.univ_nonempty_iff]; exact ne)

/--
This is where we use hull_scalar_prod. The text in [SY25] this corresponds to is:

"As noted before, Rupert’s condition and Lemma 18 imply in particular that
max_{P} ⟪ R(α) M(θ₁, φ₁), P, w ⟫ < max_{P} ⟪ M(θ₂, φ₂), P, w ⟫"
-/
private lemma hull_eq_convexHull_finset {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) :
    poly.hull = convexHull ℝ ↑(Finset.image poly.vertices.v Finset.univ) := by
  simp only [GoodPoly.hull, Polyhedron.hull, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  congr 1

theorem global_theorem_le_reasoning {ι : Type} [Fintype ι] [ne : Nonempty ι] (p : Pose ℝ)
    (poly : GoodPoly ι)
    (h_rupert : RupertPose p poly.hull) (w : ℝ²) :
    maxInner p poly w ≤ maxOuter p poly w
    := by
  let verts := Finset.image poly.vertices.v Finset.univ
  have verts_ne : verts.Nonempty := by
    simp only [verts, Finset.image_nonempty, Finset.univ_nonempty_iff]; exact ne
  have h_rupert' : RupertPose p (convexHull ℝ ↑verts) := by
    rwa [← hull_eq_convexHull_finset]
  simp only [maxInner]
  refine Finset.max'_le _ _ _ ?_
  intro y hy
  simp only [maxOuter, imgOuter]
  simp only [imgInner] at hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  change ⟪w, p.inner v⟫ ≤ (verts.image (⟪w, p.outer ·⟫)).max' _
  convert_to ⟪w, p.inner v⟫ ≤ ((verts.image p.outer).image (⟪w, ·⟫)).max' (by
      simp only [Finset.image_nonempty]; exact verts_ne)
  · simp [Finset.image_image]; rfl
  let S := p.inner v
  let V := verts.image p.outer
  have Vne : V.Nonempty := by simp only [V, Finset.image_nonempty]; exact verts_ne
  change ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) _
  refine hull_scalar_prod V Vne S ?_ w
  simp only [Finset.coe_image, V, S]
  exact p.is_rupert_imp_inner_in_outer verts h_rupert' v hv

lemma rotproj_inner_pose_eq {S : ℝ³} {w : ℝ²} (p : Pose ℝ) : rotproj_inner S w p.innerParams = ⟪p.inner S, w⟫ := by
  simp only [rotproj_inner, Pose.inner, innerProj, PoseLike.inner, Pose.innerParams,
             Matrix.cons_val_zero, Matrix.cons_val, AffineMap.coe_comp,
             LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]
  change _ = ⟪(proj_xyL ∘L rotRM p.θ₁ p.φ₁ p.α) S, w⟫
  rw [← projxy_rotRM_eq_rotprojRM]
  rfl

/--
This is the function that Theorem 17's proof calls `f`.
It always returns a unit vector.
-/
noncomputable
def GlobalTheoremPrecondition.fu {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ³ → ℝ :=
  rotproj_inner_unit pc.S pc.w

/--
This is an outer-shadow analog of `fu`
-/
noncomputable
def GlobalTheoremPrecondition.fu_outer {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} (P : ℝ³)
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ² → ℝ :=
  rotproj_outer_unit P pc.w

/--
This is the function that Theorem 17's proof calls `f`, but multiplied by ‖S‖.
-/
noncomputable
def GlobalTheoremPrecondition.f {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ³ → ℝ :=
  rotproj_inner pc.S pc.w

theorem f_pose_eq_sval {p pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.f p.innerParams = pc.Sval p := by
  simp only [GlobalTheoremPrecondition.f, GlobalTheoremPrecondition.Sval]
  rw [rotproj_inner_pose_eq]
  apply real_inner_comm

theorem f_pose_eq_inner {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.f pbar.innerParams = ⟪pbar.inner pc.S, pc.w⟫ := by
  rw [f_pose_eq_sval, GlobalTheoremPrecondition.Sval, real_inner_comm]

theorem GlobalTheoremPrecondition.fu_pose_eq_outer {p pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) {P : ℝ³} (hP : ‖P‖ ≠ 0) :
    pc.fu_outer P p.outerParams * ‖P‖ = ⟪pc.w, p.outer P⟫ := by
  simp only [GlobalTheoremPrecondition.fu_outer, rotproj_outer_unit, Pose.outer, outerProj,
           PoseLike.outer, Pose.outerParams, Matrix.cons_val,
           AffineMap.coe_comp, LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe,
           Function.comp_apply]
  rw [div_mul_cancel₀ _ hP, Pose.proj_rm_eq_m, real_inner_comm]

-- Differentiable.rotprojRM, Differentiable.rotproj_inner, rotproj_inner', rotprojRM',
-- HasFDerivAt.rotproj_inner are now imported from Noperthedron.Global.RotationPartials.Rotproj

lemma fderiv_rotproj_inner_unit (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) :
    fderiv ℝ (rotproj_inner_unit S w) pbar.innerParams = ‖S‖⁻¹ • (rotproj_inner' pbar S w) := by
  unfold rotproj_inner_unit rotprojRM
  have heq : (fun x => ⟪((rotR (x.ofLp 0)).comp (rotM (x.ofLp 1) (x.ofLp 2))) S, w⟫ / ‖S‖) =
      ‖S‖⁻¹ • (rotproj_inner S w) := by
    unfold rotproj_inner rotprojRM; ext x; simp [inv_mul_eq_div]
  rw [heq, (Differentiable.rotproj_inner S w).differentiableAt.hasFDerivAt.const_smul ‖S‖⁻¹ |>.fderiv,
    HasFDerivAt.rotproj_inner pbar S w |>.fderiv]

lemma partials_helper0a {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 0 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫ := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper0 {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 0 pc.fu pbar.innerParams =
    ⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper0a]
  field_simp

lemma partials_helper1a {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 1 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫ := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper1 {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 1 pc.fu pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper1a]
  field_simp

lemma partials_helper2a {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 2 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫ := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper2 {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 2 pc.fu pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper2a]
  field_simp

private lemma nth_partial_rotproj_outer_0 (pbar : Pose ℝ) (P : ℝ³) (w : ℝ²) :
    nth_partial 0 (rotproj_outer P w) pbar.outerParams = ⟪rotMθ pbar.θ₂ pbar.φ₂ P, w⟫ := by
  unfold nth_partial rotproj_outer
  rw [fderiv_inner_const _ w pbar.outerParams (EuclideanSpace.single 0 1)
    ((Differentiable.rotM_outer P).differentiableAt)]
  congr 1
  rw [(HasFDerivAt.rotM_outer pbar P).fderiv]
  ext i; simp

private lemma nth_partial_rotproj_outer_1 (pbar : Pose ℝ) (P : ℝ³) (w : ℝ²) :
    nth_partial 1 (rotproj_outer P w) pbar.outerParams = ⟪rotMφ pbar.θ₂ pbar.φ₂ P, w⟫ := by
  unfold nth_partial rotproj_outer
  rw [fderiv_inner_const _ w pbar.outerParams (EuclideanSpace.single 1 1)
    ((Differentiable.rotM_outer P).differentiableAt)]
  congr 1
  rw [(HasFDerivAt.rotM_outer pbar P).fderiv]
  ext i; simp

lemma partials_helper3 {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    ‖P‖ * nth_partial 0 (GlobalTheoremPrecondition.fu_outer P pc) pbar.outerParams =
    ⟪pbar.rotM₂θ P, pc.w⟫ := by
  by_cases hP : ‖P‖ = 0
  · simp [norm_eq_zero.mp hP, Pose.rotM₂θ, ContinuousLinearMap.map_zero]
  · simp only [GlobalTheoremPrecondition.fu_outer]
    rw [show rotproj_outer_unit P pc.w = fun x => rotproj_outer P pc.w x / ‖P‖ from rfl]
    rw [nth_partial_div_const 0 (rotproj_outer P pc.w) ‖P‖ pbar.outerParams
      ((Differentiable.inner ℝ (Differentiable.rotM_outer P) (differentiable_const pc.w)).differentiableAt)]
    rw [nth_partial_rotproj_outer_0]
    simp only [Pose.rotM₂θ]
    field_simp

lemma partials_helper4 {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    ‖P‖ * nth_partial 1 (GlobalTheoremPrecondition.fu_outer P pc) pbar.outerParams =
    ⟪pbar.rotM₂φ P, pc.w⟫ := by
  by_cases hP : ‖P‖ = 0
  · simp [norm_eq_zero.mp hP, Pose.rotM₂φ, ContinuousLinearMap.map_zero]
  · simp only [GlobalTheoremPrecondition.fu_outer]
    rw [show rotproj_outer_unit P pc.w = fun x => rotproj_outer P pc.w x / ‖P‖ from rfl]
    rw [nth_partial_div_const 1 (rotproj_outer P pc.w) ‖P‖ pbar.outerParams
      ((Differentiable.inner ℝ (Differentiable.rotM_outer P) (differentiable_const pc.w)).differentiableAt)]
    rw [nth_partial_rotproj_outer_1]
    simp only [Pose.rotM₂φ]
    field_simp

lemma partials_helper {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    |⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫| + |⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫| +
      |⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫| = (‖pc.S‖ * ∑ i, |nth_partial i pc.fu pbar.innerParams|) := by
  rw [Finset.mul_sum, Fin.sum_univ_three, ← abs_norm, ← abs_mul, ← abs_mul, ← abs_mul,
    partials_helper0, partials_helper1, partials_helper2]

lemma partials_helper_outer {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    |⟪pbar.rotM₂θ P, pc.w⟫| + |⟪pbar.rotM₂φ P, pc.w⟫| =
    ‖P‖ * ∑ i, |nth_partial i (pc.fu_outer P) pbar.outerParams| := by
  rw [Finset.mul_sum, Fin.sum_univ_two, ← abs_norm, ← abs_mul, ← abs_mul]
  rw [partials_helper3 pc P, partials_helper4 pc P]

private lemma innerParams_0 (pbar : Pose ℝ) : pbar.innerParams.ofLp 0 = pbar.α := by
  simp [Pose.innerParams]
private lemma innerParams_1 (pbar : Pose ℝ) : pbar.innerParams.ofLp 1 = pbar.θ₁ := by
  simp [Pose.innerParams]
private lemma innerParams_2 (pbar : Pose ℝ) : pbar.innerParams.ofLp 2 = pbar.φ₁ := by
  simp [Pose.innerParams]
private lemma outerParams_0 (pbar : Pose ℝ) : pbar.outerParams.ofLp 0 = pbar.θ₂ := by
  simp [Pose.outerParams]
private lemma outerParams_1 (pbar : Pose ℝ) : pbar.outerParams.ofLp 1 = pbar.φ₂ := by
  simp [Pose.outerParams]

private lemma second_partials_key {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} (pc : GlobalTheoremPrecondition poly pbar ε) (i j : Fin 3) :
    ‖pc.S‖ * |nth_partial i (nth_partial j pc.fu) pbar.innerParams| =
      |⟪inner_second_partial_A pbar.α pbar.θ₁ pbar.φ₁ i j pc.S, pc.w⟫| := by
  have hSne := pc.norm_S_ne_zero
  have hf_smooth : ContDiff ℝ 2 (rotproj_inner pc.S pc.w) := by
    change ContDiff ℝ 2 (fun x : ℝ³ => ⟪rotprojRM (x 1) (x 2) (x 0) pc.S, pc.w⟫)
    simp [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
    fun_prop
  have hg_diff : Differentiable ℝ (nth_partial j (rotproj_inner pc.S pc.w)) :=
    (hf_smooth.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
      contDiff_const).differentiable (by decide)
  have hdiv : nth_partial i (nth_partial j pc.fu) pbar.innerParams =
      nth_partial i (nth_partial j (rotproj_inner pc.S pc.w)) pbar.innerParams / ‖pc.S‖ :=
    nth_partial_nth_partial_div_const j i (rotproj_inner pc.S pc.w) ‖pc.S‖ pbar.innerParams
      (Differentiable.rotproj_inner pc.S pc.w) hg_diff
  rw [hdiv, second_partial_rotproj_inner_eq pc.S pc.w pbar.innerParams i j,
    innerParams_0, innerParams_1, innerParams_2, abs_div, abs_norm]
  field_simp

/-- The weighted sum of second-partial magnitudes appearing in `G` equals
`‖S‖` times the full 3×3 sum of second partials of `pc.fu` at the center. -/
lemma second_partials_helper {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} (pc : GlobalTheoremPrecondition poly pbar ε) :
    |⟪pbar.rotR (pbar.rotM₁ pc.S), pc.w⟫|
      + 2 * |⟪pbar.rotR' (pbar.rotM₁θ pc.S), pc.w⟫| + 2 * |⟪pbar.rotR' (pbar.rotM₁φ pc.S), pc.w⟫|
      + |⟪pbar.rotR (pbar.rotM₁θθ pc.S), pc.w⟫| + 2 * |⟪pbar.rotR (pbar.rotM₁θφ pc.S), pc.w⟫|
      + |⟪pbar.rotR (pbar.rotM₁φφ pc.S), pc.w⟫|
    = ‖pc.S‖ * ∑ i, ∑ j, |nth_partial i (nth_partial j pc.fu) pbar.innerParams| := by
  simp only [Fin.sum_univ_three, mul_add, second_partials_key pc]
  simp only [inner_second_partial_A, neg_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, inner_neg_left, abs_neg]
  simp only [Pose.rotR, Pose.rotR', Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ,
    Pose.rotM₁θθ, Pose.rotM₁θφ, Pose.rotM₁φφ]
  ring

private lemma second_partials_key_outer {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³)
    (hP : ‖P‖ ≠ 0) (i j : Fin 2) :
    ‖P‖ * |nth_partial i (nth_partial j (pc.fu_outer P)) pbar.outerParams| =
      |⟪outer_second_partial_A pbar.θ₂ pbar.φ₂ i j P, pc.w⟫| := by
  have hf_smooth : ContDiff ℝ 2 (fun z : ℝ² => ⟪rotM (z.ofLp 0) (z.ofLp 1) P, pc.w⟫) := by
    apply ContDiff.inner ℝ _ contDiff_const
    rw [contDiff_piLp]; intro m
    simp only [rotM, rotM_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
    fin_cases m <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> fun_prop
  have hg_diff : Differentiable ℝ
      (nth_partial j (fun z : ℝ² => ⟪rotM (z.ofLp 0) (z.ofLp 1) P, pc.w⟫)) :=
    (hf_smooth.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
      contDiff_const).differentiable (by decide)
  have hdiv : nth_partial i (nth_partial j (pc.fu_outer P)) pbar.outerParams =
      nth_partial i (nth_partial j (fun z : ℝ² => ⟪rotM (z.ofLp 0) (z.ofLp 1) P, pc.w⟫))
        pbar.outerParams / ‖P‖ :=
    nth_partial_nth_partial_div_const j i _ ‖P‖ pbar.outerParams
      (hf_smooth.differentiable (by decide)) hg_diff
  rw [hdiv, second_partial_rotproj_outer_eq P pc.w pbar.outerParams i j,
    outerParams_0, outerParams_1, abs_div, abs_norm]
  field_simp

/-- Outer analog of `second_partials_helper`. -/
lemma second_partials_helper_outer {pbar : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    |⟪pbar.rotM₂θθ P, pc.w⟫| + 2 * |⟪pbar.rotM₂θφ P, pc.w⟫| + |⟪pbar.rotM₂φφ P, pc.w⟫|
    = ‖P‖ * ∑ i, ∑ j, |nth_partial i (nth_partial j (pc.fu_outer P)) pbar.outerParams| := by
  by_cases hP : ‖P‖ = 0
  · rw [norm_eq_zero.mp hP]
    simp [Pose.rotM₂θθ, Pose.rotM₂θφ, Pose.rotM₂φφ]
  · simp only [Fin.sum_univ_two, mul_add, second_partials_key_outer pc P hP]
    simp only [outer_second_partial_A]
    simp only [Pose.rotM₂θθ, Pose.rotM₂θφ, Pose.rotM₂φφ]
    ring

theorem fu_times_norm_S_eq_f {pbar p : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.fu p.innerParams * ‖pc.S‖ = pc.f p.innerParams := by
  have := pc.norm_S_ne_zero
  simp only [GlobalTheoremPrecondition.fu, GlobalTheoremPrecondition.f, rotproj_inner_unit, rotproj_inner]
  field_simp

lemma rotproj_helper {pbar p : Pose ℝ} {ε : ℝ} {ι : Type} [Fintype ι] [Nonempty ι] {poly : GoodPoly ι}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    |pc.fu pbar.innerParams - pc.fu p.innerParams| * ‖pc.S‖ = |⟪pbar.inner pc.S, pc.w⟫ - pc.Sval p| := by
  rw [← f_pose_eq_sval, ← f_pose_eq_inner]
  repeat rw [← fu_times_norm_S_eq_f]
  rw [← sub_mul]
  simp

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_ii {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar p : Pose ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (p_near_pbar : p ∈ Metric.closedBall pbar ε)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    G pbar ε pc.S pc.w ≤ pc.Sval p := by
  have S_norm_pos : 0 < ‖pc.S‖ := pc.norm_S_gt_zero
  have S_norm_le_one : ‖pc.S‖ ≤ 1 := pc.norm_S_le_one
  have hz := bounded_partials_control_difference2
    pc.fu (rotation_partials_exist S_norm_pos)
    pbar.innerParams p.innerParams ε hε
    (closed_ball_imp_inner_params_near p_near_pbar)
    (rotation_third_partials_bounded pc.S pc.w_unit)
  simp only [G]
  refine sub_le_of_abs_sub_le_right ?_
  have h0 := mul_le_mul_of_nonneg_right hz (ha := le_of_lt S_norm_pos)
  rw [rotproj_helper pc] at h0
  have h1 : (ε * ∑ i, |nth_partial i pc.fu pbar.innerParams|
        + ε ^ 2 / 2 * ∑ i, ∑ j, |nth_partial i (nth_partial j pc.fu) pbar.innerParams|
        + ((3 : ℕ) : ℝ) ^ 3 / 6 * ε ^ 3) * ‖pc.S‖
      = ε * (‖pc.S‖ * ∑ i, |nth_partial i pc.fu pbar.innerParams|)
        + ε ^ 2 / 2 * (‖pc.S‖ * ∑ i, ∑ j, |nth_partial i (nth_partial j pc.fu) pbar.innerParams|)
        + 9 / 2 * ε ^ 3 * ‖pc.S‖ := by
    push_cast
    ring
  rw [h1, ← partials_helper pc, ← second_partials_helper pc] at h0
  refine h0.trans ?_
  have hcube : 9 / 2 * ε ^ 3 * ‖pc.S‖ ≤ 9 / 2 * ε ^ 3 := by
    nth_rewrite 2 [← mul_one (9 / 2 * ε ^ 3)]
    exact mul_le_mul_of_nonneg_left S_norm_le_one
      (mul_nonneg (by norm_num) (pow_nonneg hε 3))
  linarith

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_iv {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar p : Pose ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (p_near_pbar : p ∈ Metric.closedBall pbar ε)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    maxOuter p poly pc.w ≤ maxH pbar poly ε pc.w := by
  -- First of all, we can relate these two maximums by relating
  -- their components.
  suffices h : ∀ i : ι,
      ⟪pc.w, p.outer (poly.vertices.v i)⟫ ≤ H pbar ε pc.w (poly.vertices.v i) by
    simp only [maxOuter, maxH, imgOuter]
    apply Finset.max'_le
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine le_trans (h i) ?_
    show (H pbar ε pc.w ∘ poly.vertices.v) i ≤ _
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  -- Now we're just considering a single polyhedron vertex
  intro i
  set P := poly.vertices.v i
  have P_norm_pos : 0 < ‖P‖ := poly.nontriv i
  have P_norm_nonzero : ‖P‖ ≠ 0 := Ne.symm (ne_of_lt P_norm_pos)
  have P_norm_le_one : ‖P‖ ≤ 1 := poly.vertex_radius_le_one i

  have hz := bounded_partials_control_difference2
    (pc.fu_outer P) (rotation_partials_exist_outer P_norm_pos)
    pbar.outerParams p.outerParams ε hε
    (closed_ball_imp_outer_params_near p_near_pbar)
    (rotation_third_partials_bounded_outer P pc.w_unit)
  simp only [H]
  rw [abs_sub_comm] at hz
  replace hz := sub_le_of_abs_sub_le_right hz
  rw [tsub_le_iff_right] at hz
  replace hz := mul_le_mul_of_nonneg_right hz (ha := le_of_lt P_norm_pos)
  rw [add_mul] at hz
  rw [pc.fu_pose_eq_outer P_norm_nonzero, pc.fu_pose_eq_outer P_norm_nonzero] at hz
  have h1 : (ε * ∑ i, |nth_partial i (pc.fu_outer P) pbar.outerParams|
        + ε ^ 2 / 2 * ∑ i, ∑ j, |nth_partial i (nth_partial j (pc.fu_outer P)) pbar.outerParams|
        + ((2 : ℕ) : ℝ) ^ 3 / 6 * ε ^ 3) * ‖P‖
      = ε * (‖P‖ * ∑ i, |nth_partial i (pc.fu_outer P) pbar.outerParams|)
        + ε ^ 2 / 2 * (‖P‖ * ∑ i, ∑ j, |nth_partial i (nth_partial j (pc.fu_outer P)) pbar.outerParams|)
        + 4 / 3 * ε ^ 3 * ‖P‖ := by
    push_cast
    ring
  rw [h1, ← partials_helper_outer pc P, ← second_partials_helper_outer pc P] at hz
  rw [show pbar.rotM₂ P = pbar.outer P by rw [Pose.outer_eq_M]]
  rw [real_inner_comm pc.w (pbar.outer P)]
  have hcube : 4 / 3 * ε ^ 3 * ‖P‖ ≤ 4 / 3 * ε ^ 3 := by
    nth_rewrite 2 [← mul_one (4 / 3 * ε ^ 3)]
    exact mul_le_mul_of_nonneg_left P_norm_le_one
      (mul_nonneg (by norm_num) (pow_nonneg hε 3))
  linarith

/--
Here we run through the "sequence of inequalities [which yield] the desired contradiction"
-/
theorem global_theorem_gt_reasoning {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar p : Pose ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (p_near_pbar : p ∈ Metric.closedBall pbar ε)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    maxInner p poly pc.w > maxOuter p poly pc.w := by
  have sval_in_img_inner : pc.Sval p ∈ imgInner p (Finset.image poly.vertices.v Finset.univ) pc.w := by
    simp only [Finset.mem_image, imgInner, GlobalTheoremPrecondition.Sval, Finset.mem_univ,
      true_and]
    exact ⟨pc.S, ⟨pc.Si, rfl⟩, rfl⟩
  calc
    maxInner p poly pc.w
    _ ≥ pc.Sval p := Finset.le_max' (H2 := sval_in_img_inner)
    _ ≥ G pbar ε pc.S pc.w := global_theorem_inequality_ii pbar p ε hε p_near_pbar poly pc
    _ > maxH pbar poly ε pc.w := pc.exceeds
    _ ≥ maxOuter p poly pc.w := global_theorem_inequality_iv pbar p ε hε p_near_pbar poly pc

/--
The Global Theorem, [SY25] Theorem 17
-/
theorem global_theorem {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar : Pose ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ¬ ∃ p ∈ Metric.closedBall pbar ε, RupertPose p poly.hull := by
  rintro ⟨p, p_near_pbar, p_is_rupert⟩
  have hgt := global_theorem_gt_reasoning pbar p ε hε p_near_pbar poly pc
  have hle := global_theorem_le_reasoning p poly p_is_rupert pc.w
  exact lt_irrefl _ (lt_of_lt_of_le hgt hle)

end GlobalTheorem
