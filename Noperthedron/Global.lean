import Noperthedron.Global.RotationPartials

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

/- [SY25] Lemma 18 -/
theorem hull_scalar_prod {n : ℕ} (V : Finset (E n)) (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (w : E n) :
    ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) (by simp [Finset.image_nonempty]; exact Vne) := by
  exact finset_hull_linear_max Vne S hs (InnerProductSpace.toDual ℝ (E n) w |>.toLinearMap)


-- NOTE: The HasDerivAt_rotR', fderiv_rotR_rotM_in_e0/e1/e2, fderiv_rotR'_rotM_in_e0/e1,
-- and fderiv_rotR_any_M_in_e0 lemmas are now defined in Global/FDerivHelpers.lean

/--
A measure of how far an inner-shadow vertex S can "stick out"
-/
noncomputable
def G (p : Pose) (ε : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.inner S, w⟫ - (ε * (|⟪p.rotR' (p.rotM₁ S), w⟫| + |⟪p.rotR (p.rotM₁θ S), w⟫| + |⟪p.rotR (p.rotM₁φ S), w⟫|)
  + 9 * ε^2 / 2)

/--
A measure of how far an outer-shadow vertex P can "reach" along w.
-/
noncomputable
def H (p : Pose) (ε : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ P, w⟫ + ε * (|⟪p.rotM₂θ P, w⟫| + |⟪p.rotM₂φ P, w⟫|) + 2 * ε^2

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

theorem GlobalTheoremPrecondition.norm_S_gt_zero
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : 0 < ‖hp.S‖ :=
  poly.nontriv hp.S hp.S_in_poly

theorem GlobalTheoremPrecondition.norm_S_ne_zero
    {poly : GoodPoly} {p : Pose} {ε : ℝ}
    (hp : GlobalTheoremPrecondition poly p ε) : 0 ≠ ‖hp.S‖ :=
  ne_of_lt hp.norm_S_gt_zero

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

lemma rotproj_inner_pose_eq {S : ℝ³} {w : ℝ²} (p : Pose) : rotproj_inner S w p.innerParams = ⟪p.inner S, w⟫ := by
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
def GlobalTheoremPrecondition.fu {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ³ → ℝ :=
  rotproj_inner_unit pc.S pc.w

/--
This is an outer-shadow analog of `fu`
-/
noncomputable
def GlobalTheoremPrecondition.fu_outer {pbar : Pose} {ε : ℝ} {poly : GoodPoly} (P : ℝ³)
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ² → ℝ :=
  rotproj_outer_unit P pc.w

/--
This is the function that Theorem 17's proof calls `f`, but multiplied by ‖S‖.
-/
noncomputable
def GlobalTheoremPrecondition.f {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) : ℝ³ → ℝ :=
  rotproj_inner pc.S pc.w

theorem f_pose_eq_sval {p pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.f p.innerParams = pc.Sval p := by
  simp [GlobalTheoremPrecondition.f, GlobalTheoremPrecondition.Sval]
  rw [rotproj_inner_pose_eq]
  apply real_inner_comm

theorem f_pose_eq_inner {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.f pbar.innerParams = ⟪pbar.inner pc.S, pc.w⟫ := by
  rw [f_pose_eq_sval, GlobalTheoremPrecondition.Sval, real_inner_comm]

theorem GlobalTheoremPrecondition.fu_pose_eq_outer {p pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    pc.fu_outer P p.outerParams * ‖P‖ = ⟪pc.w, p.outer P⟫ := by
  simp only [GlobalTheoremPrecondition.fu_outer, rotproj_outer_unit, Pose.outer, outerProj,
             PoseLike.outer, Pose.outerParams, Matrix.cons_val_zero, Matrix.cons_val,
             AffineMap.coe_comp, LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe,
             Function.comp_apply]
  by_cases hP : P = 0
  · simp [hP]
  · rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hP), Pose.proj_rm_eq_m, real_inner_comm]

lemma Differentiable.rotproj_outer (P : ℝ³) (w : ℝ²) : Differentiable ℝ (rotproj_outer P w) :=
  Differentiable.inner ℝ (Differentiable.rotM_outer P) (by fun_prop)

lemma HasFDerivAt.rotproj_outer (pbar : Pose) (P : ℝ³) (w : ℝ²) :
    HasFDerivAt (rotproj_outer P w) (rotproj_outer' pbar P w) pbar.outerParams := by
  have z1 : HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams :=
    HasFDerivAt.rotM_outer pbar P
  have step :
    rotproj_outer' pbar P w = (fderivInnerCLM ℝ
        ((rotM (pbar.outerParams.ofLp 0) (pbar.outerParams.ofLp 1)) P, w)).comp
        ((rotM' pbar P).prod 0) := by
    ext d
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
               ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add, real_inner_comm]
    simp only [rotproj_outer', rotM']
    simp only [LinearMap.coe_toContinuousLinearMap']
    simp only [Module.Basis.constr_apply_fintype]
    simp only [Matrix.toEuclideanLin_apply]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_lhs => rw [show (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.equivFun = (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)) by
      rw [EuclideanSpace.basisFun_toBasis]; exact @PiLp.basisFun_equivFun 2 ℝ (Fin 2) _ _]
    simp only [WithLp.linearEquiv_apply]
    simp only [WithLp.addEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
    conv_rhs => simp only [Matrix.mulVec, Matrix.of_apply]
    simp only [PiLp.inner_apply, Matrix.mulVec, Matrix.of_apply,
               Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    unfold dotProduct
    simp only [Fin.sum_univ_two, smul_eq_mul, Pose.rotM₂θ, Pose.rotM₂φ]
    ring
  rw [step]
  exact HasFDerivAt.inner ℝ z1 (hasFDerivAt_const w pbar.outerParams)

lemma fderiv_rotproj_outer_unit (pbar : Pose) (P : ℝ³) (w : ℝ²) :
    fderiv ℝ (rotproj_outer_unit P w) pbar.outerParams = ‖P‖⁻¹ • (rotproj_outer' pbar P w) := by
  have heq : rotproj_outer_unit P w = ‖P‖⁻¹ • rotproj_outer P w := by
    ext x; simp [rotproj_outer_unit, rotproj_outer, inv_mul_eq_div]
  simp only [heq, HasFDerivAt.rotproj_outer pbar P w |>.const_smul ‖P‖⁻¹ |>.fderiv]

lemma partials_helper3a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    (fderiv ℝ (rotproj_outer_unit P pc.w) pbar.outerParams) (EuclideanSpace.single 0 1) =
    ‖P‖⁻¹ * ⟪pbar.rotM₂θ P, pc.w⟫ := by
  rw [fderiv_rotproj_outer_unit pbar P pc.w]
  simp [rotproj_outer']

lemma partials_helper4a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) :
    (fderiv ℝ (rotproj_outer_unit P pc.w) pbar.outerParams) (EuclideanSpace.single 1 1) =
    ‖P‖⁻¹ * ⟪pbar.rotM₂φ P, pc.w⟫ := by
  rw [fderiv_rotproj_outer_unit pbar P pc.w]
  simp [rotproj_outer']

lemma fderiv_rotproj_inner_unit (pbar : Pose) (S : ℝ³) (w : ℝ²) :
    fderiv ℝ (rotproj_inner_unit S w) pbar.innerParams = ‖S‖⁻¹ • (rotproj_inner' pbar S w) := by
  have heq : rotproj_inner_unit S w = ‖S‖⁻¹ • rotproj_inner S w := by
    ext x; simp [rotproj_inner_unit, rotproj_inner, inv_mul_eq_div]
  simp only [heq, HasFDerivAt.rotproj_inner pbar S w |>.const_smul ‖S‖⁻¹ |>.fderiv]

lemma partials_helper0a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 0 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫  := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper0 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 0 pc.fu pbar.innerParams =
    ⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper0a]
  field_simp

lemma partials_helper1a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 1 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫  := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper1 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 1 pc.fu pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper1a]
  field_simp

lemma partials_helper2a {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    (fderiv ℝ (rotproj_inner_unit pc.S pc.w) pbar.innerParams) (EuclideanSpace.single 2 1) =
    ‖pc.S‖⁻¹ * ⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫  := by
  rw [fderiv_rotproj_inner_unit pbar pc.S pc.w]
  simp [rotproj_inner']

lemma partials_helper2 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    ‖pc.S‖ * nth_partial 2 pc.fu pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫ := by
  have := pc.norm_S_ne_zero
  simp only [nth_partial, GlobalTheoremPrecondition.fu, Fin.isValue, partials_helper2a]
  field_simp

lemma partials_helper3 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) (hP : ‖P‖ ≠ 0) :
    ‖P‖ * nth_partial 0 (GlobalTheoremPrecondition.fu_outer P pc) pbar.outerParams =
    ⟪pbar.rotM₂θ P, pc.w⟫ := by
  simp only [nth_partial, GlobalTheoremPrecondition.fu_outer, Fin.isValue, partials_helper3a]
  field_simp [hP]

lemma partials_helper4 {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) (hP : ‖P‖ ≠ 0) :
    ‖P‖ * nth_partial 1 (GlobalTheoremPrecondition.fu_outer P pc) pbar.outerParams =
    ⟪pbar.rotM₂φ P, pc.w⟫ := by
  simp only [nth_partial, GlobalTheoremPrecondition.fu_outer, Fin.isValue, partials_helper4a]
  field_simp [hP]

lemma partials_helper {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    |⟪pbar.rotR' (pbar.rotM₁ pc.S), pc.w⟫| + |⟪pbar.rotR (pbar.rotM₁θ pc.S), pc.w⟫| +
      |⟪pbar.rotR (pbar.rotM₁φ pc.S), pc.w⟫| = (‖pc.S‖ * ∑ i, |nth_partial i pc.fu pbar.innerParams|) := by
  rw [Finset.mul_sum, Fin.sum_univ_three, ← abs_norm, ← abs_mul, ← abs_mul, ← abs_mul,
    partials_helper0, partials_helper1, partials_helper2]

lemma partials_helper_outer {pbar : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) (P : ℝ³) (hP : ‖P‖ ≠ 0) :
    |⟪pbar.rotM₂θ P, pc.w⟫| + |⟪pbar.rotM₂φ P, pc.w⟫| =
    ‖P‖ * ∑ i, |nth_partial i (pc.fu_outer P) pbar.outerParams| := by
  rw [Finset.mul_sum, Fin.sum_univ_two, ← abs_norm, ← abs_mul, ← abs_mul]
  simp only [Fin.isValue]
  rw [partials_helper3 pc P hP, partials_helper4 pc P hP]

theorem fu_times_norm_S_eq_f {pbar p : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    pc.fu p.innerParams * ‖pc.S‖ = pc.f p.innerParams := by
  have := pc.norm_S_ne_zero
  simp only [GlobalTheoremPrecondition.fu, GlobalTheoremPrecondition.f, rotproj_inner_unit, rotproj_inner]
  field_simp

lemma rotproj_helper {pbar p : Pose} {ε : ℝ} {poly : GoodPoly}
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    |pc.fu pbar.innerParams - pc.fu p.innerParams| * ‖pc.S‖ = |⟪pbar.inner pc.S, pc.w⟫ - pc.Sval p| := by
  rw [← f_pose_eq_sval, ← f_pose_eq_inner]
  repeat rw [← fu_times_norm_S_eq_f]
  rw [← sub_mul]
  simp

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_ii (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    G pbar ε pc.S pc.w ≤ pc.Sval p := by
  have S_norm_pos : 0 < ‖pc.S‖ := pc.norm_S_gt_zero
  have S_norm_le_one : ‖pc.S‖ ≤ 1 := pc.norm_S_le_one
  have hz := bounded_partials_control_difference
    pc.fu (rotation_partials_exist S_norm_pos)
    pbar.innerParams p.innerParams ε hε
    (closed_ball_imp_inner_params_near p_near_pbar)
    (rotation_partials_bounded pc.S pc.w_unit)
  simp only [G]
  refine sub_le_of_abs_sub_le_right ?_
  have hzs := mul_le_mul_of_nonneg_right hz (ha := le_of_lt S_norm_pos)
  rw [← rotproj_helper pc, partials_helper pc]
  norm_num at hzs
  ring_nf at hzs ⊢
  nth_grw 3 [S_norm_le_one] at hzs
  simp_all only [one_mul]

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_iv (pbar p : Pose) (ε : ℝ) (hε : ε > 0)
    (p_near_pbar : p ∈ pbar.closed_ball ε)
    (poly : GoodPoly)
    (pc : GlobalTheoremPrecondition poly pbar ε) :
    maxOuter p poly pc.w ≤ maxH pbar poly ε pc.w := by
  -- First of all, we can relate these two maximums by relating
  -- their components.
  suffices h : ∀ vert ∈ poly.vertices,
      ⟪pc.w, p.outer vert⟫ ≤ H pbar ε pc.w vert by
    simp only [maxH, maxOuter, imgOuter, Finset.max'_le_iff, Finset.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    simp only [Finset.max', Finset.sup'_image,
      Finset.le_sup'_iff]
    exact fun a ha => Exists.intro a ⟨ha, h a ha⟩
  -- Now we're just considering a single polyhedron vertex P
  intro P hP
  have P_norm_pos : 0 < ‖P‖ := poly.nontriv P hP
  have P_norm_le_one : ‖P‖ ≤ 1 := poly.vertex_radius_le_one P hP

  have hz := bounded_partials_control_difference
    (pc.fu_outer P) (rotation_partials_exist_outer P_norm_pos)
    pbar.outerParams p.outerParams ε hε
    (closed_ball_imp_outer_params_near p_near_pbar)
    (rotation_partials_bounded_outer P pc.w_unit)
  simp_all only [H]
  rw [abs_sub_comm] at hz
  replace hz := sub_le_of_abs_sub_le_right hz
  rw [tsub_le_iff_right] at hz
  replace hz := mul_le_mul_of_nonneg_right hz (ha := le_of_lt P_norm_pos)
  rw [add_mul] at hz
  rw [pc.fu_pose_eq_outer P, pc.fu_pose_eq_outer P] at hz
  rw [partials_helper_outer pc P (ne_of_gt P_norm_pos)]
  rw [show pbar.rotM₂ P = pbar.outer P by rw [Pose.outer_eq_M]]
  conv => enter [2, 1, 1]; rw [real_inner_comm]
  ring_nf at hz ⊢
  nth_grw 2 [P_norm_le_one] at hz
  simp only [mul_one] at hz
  exact hz

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
