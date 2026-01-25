import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Noperthedron.Nopert
import Noperthedron.PoseInterval
import Noperthedron.Global.Basic
import Noperthedron.Global.BoundedPartialsControlDifference

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

noncomputable
def rotproj_inner (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫

noncomputable
def rotproj_inner_unit (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫ / ‖S‖

noncomputable
def rotproj_outer_unit (S : ℝ³) (w : ℝ²) (x : ℝ²) : ℝ :=
  ⟪rotM (x 0) (x 1) S, w⟫ / ‖S‖

noncomputable
def rotproj_outer (S : ℝ³) (w : ℝ²) (x : ℝ²) : ℝ :=
  ⟪rotM (x 0) (x 1) S, w⟫

/--
An explicit formula for the full derivative of rotproj_outer as a function ℝ² → ℝ
-/
noncomputable
def rotproj_outer' (pbar : Pose) (P : ℝ³) (w : ℝ²) : ℝ² →L[ℝ] ℝ :=
  let grad : Fin 2 → ℝ := ![
    ⟪pbar.rotM₂θ P, w⟫,
    ⟪pbar.rotM₂φ P, w⟫
  ]
  EuclideanSpace.basisFun (Fin 2) ℝ |>.toBasis.constr ℝ grad |>.toContinuousLinearMap

lemma rotation_partials_exist {S : ℝ³} (S_nonzero : ‖S‖ > 0) {w : ℝ²} :
    ContDiff ℝ 2 (rotproj_inner_unit S w) := by
  refine ContDiff.div ?_ contDiff_const (fun x ↦ (ne_of_lt S_nonzero).symm)
  simp [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

lemma rotation_partials_exist_outer {S : ℝ³} (S_nonzero : ‖S‖ > 0) {w : ℝ²} :
    ContDiff ℝ 2 (rotproj_outer_unit S w) := by
  refine ContDiff.div ?_ contDiff_const (fun x ↦ (ne_of_lt S_nonzero).symm)
  simp [inner, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

/- [SY25] Lemma 19 -/
theorem rotation_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_inner_unit S w) := by
  sorry

theorem rotation_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_outer_unit S w) := by
  sorry

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

lemma Differentiable.rotprojRM (S : ℝ³) :
    Differentiable ℝ fun (x : ℝ³)  ↦ (_root_.rotprojRM (x 1) (x 2) (x 0)) S := by
  unfold _root_.rotprojRM
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

@[fun_prop]
lemma Differentiable.rotproj_inner (S : ℝ³) (w : ℝ²) : Differentiable ℝ (rotproj_inner S w) :=
  Differentiable.inner ℝ (Differentiable.rotprojRM S) (by fun_prop)

/--
An explicit formula for the full derivative of rotproj_inner as a function ℝ³ → ℝ
-/
noncomputable
def rotproj_inner' (pbar : Pose) (S : ℝ³) (w : ℝ²) : ℝ³ →L[ℝ] ℝ :=
  let grad : Fin 3 → ℝ := ![
    ⟪pbar.rotR' (pbar.rotM₁ S), w⟫,
    ⟪pbar.rotR (pbar.rotM₁θ S), w⟫,
    ⟪pbar.rotR (pbar.rotM₁φ S), w⟫
  ]
  EuclideanSpace.basisFun (Fin 3) ℝ |>.toBasis.constr ℝ grad |>.toContinuousLinearMap

/--
The Fréchet derivative of `fun x => rotprojRM (x 1) (x 2) (x 0) S` at `pbar.innerParams`.
Components:
- index 0 (α): rotR' α (rotM θ φ S)
- index 1 (θ): rotR α (rotMθ θ φ S)
- index 2 (φ): rotR α (rotMφ θ φ S)
-/
noncomputable
def rotprojRM' (pbar : Pose) (S : ℝ³) : ℝ³ →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 3) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (pbar.rotR' (pbar.rotM₁ S)) i
    | 1 => (pbar.rotR (pbar.rotM₁θ S)) i
    | 2 => (pbar.rotR (pbar.rotM₁φ S)) i
  M.toEuclideanLin.toContinuousLinearMap

-- Helper lemma: component 0 of rotprojRM in terms of sin/cos
private lemma rotprojRM_component0 (θ φ α : ℝ) (S : ℝ³) :
    (rotprojRM θ φ α S) 0 =
      Real.cos α * (-Real.sin θ * S 0 + Real.cos θ * S 1) -
      Real.sin α * (-Real.cos θ * Real.cos φ * S 0 - Real.sin θ * Real.cos φ * S 1 + Real.sin φ * S 2) := by
  simp [rotprojRM, rotR, rotM, rotR_mat, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  ring

-- Helper lemma: component 1 of rotprojRM in terms of sin/cos
private lemma rotprojRM_component1 (θ φ α : ℝ) (S : ℝ³) :
    (rotprojRM θ φ α S) 1 =
      Real.sin α * (-Real.sin θ * S 0 + Real.cos θ * S 1) +
      Real.cos α * (-Real.cos θ * Real.cos φ * S 0 - Real.sin θ * Real.cos φ * S 1 + Real.sin φ * S 2) := by
  simp [rotprojRM, rotR, rotM, rotR_mat, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  ring

lemma HasFDerivAt.rotproj_inner (pbar : Pose) (S : ℝ³) (w : ℝ²) :
    (HasFDerivAt (rotproj_inner S w) (rotproj_inner' pbar S w) pbar.innerParams) := by

  have z1 : HasFDerivAt (fun x => (rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S) (rotprojRM' pbar S) pbar.innerParams := by
    -- Prove using HasStrictFDerivAt for each component and then combine
    -- The function is f(α, θ, φ) = rotR α (rotM θ φ S)
    -- Jacobian has columns: ∂/∂α = rotR' α (rotM θ φ S), ∂/∂θ = rotR α (rotMθ θ φ S), ∂/∂φ = rotR α (rotMφ θ φ S)
    apply HasStrictFDerivAt.hasFDerivAt
    rw [hasStrictFDerivAt_piLp]
    intro i
    fin_cases i <;> {
      simp only [Fin.isValue]
      simp only [rotprojRM', Pose.rotR', Pose.rotR, Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ,
        rotR', rotR'_mat, rotR, rotR_mat, rotM, rotMθ, rotMφ, rotM_mat]
      simp only [rotprojRM, ContinuousLinearMap.coe_comp', Function.comp_apply]
      -- The component function is a polynomial in sin/cos of α, θ, φ
      -- Its derivative is computed via chain rule
      -- TODO: Fill in with detailed derivative computation using HasStrictFDerivAt.mul, .add, etc.
      sorry
    }

  have step :
    (rotproj_inner' pbar S w) = ((fderivInnerCLM ℝ
            ((rotprojRM (pbar.innerParams.ofLp 1) (pbar.innerParams.ofLp 2) (pbar.innerParams.ofLp 0)) S, w)).comp
        ((rotprojRM' pbar S).prod 0)) := by
    ext d
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
               ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add, real_inner_comm]
    simp only [rotproj_inner', rotprojRM']
    simp only [LinearMap.coe_toContinuousLinearMap']
    simp only [Module.Basis.constr_apply_fintype]
    simp only [Matrix.toEuclideanLin_apply]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_lhs => rw [show (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.equivFun = (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) by
      rw [EuclideanSpace.basisFun_toBasis]; exact @PiLp.basisFun_equivFun 2 ℝ (Fin 3) _ _]
    simp only [WithLp.linearEquiv_apply]
    simp only [WithLp.addEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
    simp only [Fin.isValue, Matrix.cons_val]
    conv_rhs => simp only [Matrix.mulVec, Matrix.of_apply]
    simp only [PiLp.inner_apply, Matrix.mulVec, Matrix.of_apply,
               Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    unfold dotProduct
    simp only [Fin.sum_univ_three, smul_eq_mul]
    ring

  rw [step]
  exact HasFDerivAt.inner ℝ z1 (hasFDerivAt_const w pbar.innerParams)

/-- The fderiv of rotM applied to a fixed vector P, as a function of (θ, φ). -/
noncomputable
def rotM' (pbar : Pose) (P : ℝ³) : ℝ² →L[ℝ] ℝ² :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => (rotMθ pbar.θ₂ pbar.φ₂ P) i
    | 1 => (rotMφ pbar.θ₂ pbar.φ₂ P) i
  M.toEuclideanLin.toContinuousLinearMap

lemma Differentiable.rotM_outer (P : ℝ³) :
    Differentiable ℝ fun (x : ℝ²) => (rotM (x 0) (x 1)) P := by
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

private lemma rotM_component0 (θ φ : ℝ) (P : ℝ³) :
    (rotM θ φ P) 0 = -Real.sin θ * P 0 + Real.cos θ * P 1 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]

private lemma rotM_component1 (θ φ : ℝ) (P : ℝ³) :
    (rotM θ φ P) 1 = -Real.cos θ * Real.cos φ * P 0 - Real.sin θ * Real.cos φ * P 1 + Real.sin φ * P 2 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one]
  ring

lemma HasFDerivAt.rotM_outer (pbar : Pose) (P : ℝ³) :
    HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams := by
  -- Use hasStrictFDerivAt_piLp to decompose into components, then convert to hasFDerivAt
  apply HasStrictFDerivAt.hasFDerivAt
  rw [hasStrictFDerivAt_piLp]
  intro i
  fin_cases i
  · -- Component 0: f(θ, φ) = -sin θ * P[0] + cos θ * P[1] (only depends on θ)
    simp only [Fin.isValue]
    -- Rewrite function using component lemma
    have hfunc : (fun x : ℝ² => ((rotM (x.ofLp 0) (x.ofLp 1)) P).ofLp (0 : Fin 2)) =
        fun x => -Real.sin (x.ofLp 0) * P 0 + Real.cos (x.ofLp 0) * P 1 := by
      ext x
      exact rotM_component0 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl]
    rw [hfunc]
    -- The derivative: d ↦ (-cos θ * P[0] - sin θ * P[1]) * d[0]
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp (rotM' pbar P) =
        ((-Real.cos pbar.θ₂ * P 0 - Real.sin pbar.θ₂ * P 1) • PiLp.proj 2 (fun _ => ℝ) 0) := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Fin.isValue]
      -- Expand rotMθ and rotMφ at component 0
      simp only [rotMθ, rotMφ, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      -- Evaluate the matrix row entries: ![a, b, c] 2 = c
      rw [show ![-Real.cos pbar.θ₂, -Real.sin pbar.θ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![(0 : ℝ), 0, 0] (2 : Fin 3) = 0 from rfl]
      ring
    rw [hderiv]
    -- Now prove: HasStrictFDerivAt (fun x => -sin(x 0) * P 0 + cos(x 0) * P 1)
    --            ((c) • proj 0) pbar.outerParams
    let proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
    have hsin : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
        (Real.cos pbar.θ₂ • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_sin pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hcos : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams := by
      have h := Real.hasStrictDerivAt_cos pbar.θ₂
      exact h.comp_hasStrictFDerivAt pbar.outerParams hproj0
    have hf : HasStrictFDerivAt (fun x : ℝ² => -Real.sin (x.ofLp 0) * P 0 + Real.cos (x.ofLp 0) * P 1)
        ((-Real.cos pbar.θ₂ * P 0 - Real.sin pbar.θ₂ * P 1) • proj0)
        pbar.outerParams := by
      -- Using mul_const: HasStrictFDerivAt (fun y => c y * d) (d • c') x
      have h1 : HasStrictFDerivAt (fun x : ℝ² => -Real.sin (x.ofLp 0) * P 0)
          ((P 0) • -(Real.cos pbar.θ₂ • proj0)) pbar.outerParams :=
        hsin.neg.mul_const (P 0)
      have h2 : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * P 1)
          ((P 1) • -(Real.sin pbar.θ₂ • proj0)) pbar.outerParams := by
        have := hcos.mul_const (P 1)
        -- Need to convert P 1 • -sin • proj0 to P 1 • -(sin • proj0)
        rw [show (P 1) • -(Real.sin pbar.θ₂ • proj0) = (P 1) • -Real.sin pbar.θ₂ • proj0 by
          rw [neg_smul]]
        exact this
      have hadd := h1.add h2
      convert hadd using 1
      ext d
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
                 ContinuousLinearMap.neg_apply, neg_mul]
      ring
    exact hf
  · -- Component 1: f(θ, φ) = -cos θ cos φ * P[0] - sin θ cos φ * P[1] + sin φ * P[2]
    simp only [Fin.isValue]
    -- Rewrite function using component lemma
    have hfunc : (fun x : ℝ² => ((rotM (x.ofLp 0) (x.ofLp 1)) P).ofLp (1 : Fin 2)) =
        fun x => -Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0
               - Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1
               + Real.sin (x.ofLp 1) * P 2 := by
      ext x
      exact rotM_component1 (x.ofLp 0) (x.ofLp 1) P
    simp only [show (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) from rfl]
    rw [hfunc]
    -- Derivative structure: ∂/∂θ and ∂/∂φ combined
    have hderiv : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp (rotM' pbar P) =
        (Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 0 - Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 1) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        (Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 1 + Real.cos pbar.φ₂ * P 2) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Fin.isValue]
      simp only [rotMθ, rotMφ, LinearMap.coe_toContinuousLinearMap',
                 Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
                 Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
                 Matrix.of_apply, Fin.isValue]
      rw [show ![Real.sin pbar.θ₂ * Real.cos pbar.φ₂, -Real.cos pbar.θ₂ * Real.cos pbar.φ₂, (0 : ℝ)] (2 : Fin 3) = 0 from rfl]
      rw [show ![Real.cos pbar.θ₂ * Real.sin pbar.φ₂, Real.sin pbar.θ₂ * Real.sin pbar.φ₂, Real.cos pbar.φ₂] (2 : Fin 3) = Real.cos pbar.φ₂ from rfl]
      ring
    rw [hderiv]
    -- Use the chain rule for both variables
    let proj0 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    let proj1 : ℝ² →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 0) proj0 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 0
    have hproj1 : HasStrictFDerivAt (fun x : ℝ² => x.ofLp 1) proj1 pbar.outerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.outerParams 1
    -- Individual derivatives - need to prove pbar.outerParams.ofLp i = pbar.θ₂/φ₂
    have hθ : pbar.outerParams.ofLp 0 = pbar.θ₂ := by simp [Pose.outerParams]
    have hφ : pbar.outerParams.ofLp 1 = pbar.φ₂ := by simp [Pose.outerParams]
    have hsinθ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0))
        (Real.cos pbar.θ₂ • proj0) pbar.outerParams :=
      (Real.hasStrictDerivAt_sin pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0 hθ.symm
    have hcosθ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.θ₂) • proj0) pbar.outerParams :=
      (Real.hasStrictDerivAt_cos pbar.θ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj0 hθ.symm
    have hsinφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 1))
        (Real.cos pbar.φ₂ • proj1) pbar.outerParams :=
      (Real.hasStrictDerivAt_sin pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1 hφ.symm
    have hcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 1))
        (-(Real.sin pbar.φ₂) • proj1) pbar.outerParams :=
      (Real.hasStrictDerivAt_cos pbar.φ₂).comp_hasStrictFDerivAt_of_eq pbar.outerParams hproj1 hφ.symm
    -- The full derivative combines all terms
    -- This is complex - use convert to match the expected form
    have hf : HasStrictFDerivAt
        (fun x => -Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1) * P 0
                - Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1) * P 1
                + Real.sin (x.ofLp 1) * P 2)
        ((Real.sin pbar.θ₂ * Real.cos pbar.φ₂ * P 0 - Real.cos pbar.θ₂ * Real.cos pbar.φ₂ * P 1) • proj0 +
         (Real.cos pbar.θ₂ * Real.sin pbar.φ₂ * P 0 + Real.sin pbar.θ₂ * Real.sin pbar.φ₂ * P 1 + Real.cos pbar.φ₂ * P 2) • proj1)
        pbar.outerParams := by
      -- Build using product rule: d(f*g) = f(x)·g' + g(x)·f'
      -- Product of cos(θ) * cos(φ)
      have hcosθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1))
          (Real.cos pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (-(Real.sin pbar.θ₂) • proj0))
          pbar.outerParams := hcosθ.mul hcosφ
      -- Product of sin(θ) * cos(φ)
      have hsinθcosφ : HasStrictFDerivAt (fun x : ℝ² => Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1))
          (Real.sin pbar.θ₂ • (-(Real.sin pbar.φ₂) • proj1) + Real.cos pbar.φ₂ • (Real.cos pbar.θ₂ • proj0))
          pbar.outerParams := hsinθ.mul hcosφ
      -- Combined using add/sub/mul_const
      have hadd := ((hcosθcosφ.neg.mul_const (P 0)).sub (hsinθcosφ.mul_const (P 1))).add (hsinφ.mul_const (P 2))
      convert hadd using 1
      · -- Function equality
        ext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
        ring
      · -- Derivative equality
        ext d
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
                   ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
        ring
    exact hf

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
