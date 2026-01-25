import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Noperthedron.RotationDerivs
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

-- Key bound lemma for inner product with rotation matrices
private lemma inner_product_norm_bound (A : ℝ³ →L[ℝ] ℝ²) (S : ℝ³) (w : ℝ²)
    (hA : ‖A‖ ≤ 1) : |⟪A S, w⟫| ≤ ‖S‖ * ‖w‖ := by
  calc |⟪A S, w⟫|
    _ ≤ ‖A S‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖A‖ * ‖S‖ * ‖w‖ := by
        apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ 1 * ‖S‖ * ‖w‖ := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖S‖ * ‖w‖ := by ring

private lemma inner_bound_helper (A : ℝ³ →L[ℝ] ℝ²) (S : ℝ³) (w : ℝ²)
    (hw : ‖w‖ = 1) (hA : ‖A‖ ≤ 1) : |⟪A S, w⟫ / ‖S‖| ≤ 1 := by
  by_cases hS : ‖S‖ = 0
  · simp [hS]
  · rw [abs_div, abs_norm]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    calc |⟪A S, w⟫|
      _ ≤ ‖A S‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖S‖ * ‖w‖ := by
          apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ 1 * ‖S‖ * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (le_of_eq hw)
            (norm_nonneg _)
          positivity
      _ = ‖S‖ := by ring

-- Derivatives of rotation matrix partials w.r.t. angles
-- These are needed for computing second derivatives of rotproj functions
-- Each proves HasDerivAt for the rotation matrix derivative applied to a fixed vector S

-- The proofs follow by expanding the matrix definitions and differentiating component-wise
-- using HasDerivAt.add, HasDerivAt.mul_const, Real.hasDerivAt_sin, Real.hasDerivAt_cos
private lemma hasDerivAt_rotMθ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθ θ' φ S) (rotMθθ θ φ S) θ := by
  have h_f : (fun θ' => rotMθ θ' φ S) = (fun θ' => !₂[-Real.cos θ' * S 0 - Real.sin θ' * S 1,
      Real.sin θ' * Real.cos φ * S 0 - Real.cos θ' * Real.cos φ * S 1]) := by
    ext θ' i; fin_cases i <;> simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMθθ θ φ S = !₂[Real.sin θ * S 0 - Real.cos θ * S 1,
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · have h : deriv (fun x => -Real.cos x * S 0 - Real.sin x * S 1) θ = Real.sin θ * S 0 - Real.cos θ * S 1 := by simp
    rw [← h]; exact DifferentiableAt.hasDerivAt (by fun_prop)
  · have h1 : HasDerivAt (fun x => Real.sin x * Real.cos φ * S 0) (Real.cos θ * Real.cos φ * S 0) θ := by
      have := (Real.hasDerivAt_sin θ).mul_const (Real.cos φ * S 0); simp only [mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.cos x * Real.cos φ * S 1) (-Real.sin θ * Real.cos φ * S 1) θ := by
      have := (Real.hasDerivAt_cos θ).mul_const (Real.cos φ * S 1); simp only [mul_assoc, neg_mul] at this ⊢; exact this
    convert h1.sub h2 using 1; ring

private lemma hasDerivAt_rotMθ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθ θ φ' S) (rotMθφ θ φ S) φ := by
  have h_f : (fun φ' => rotMθ θ φ' S) = (fun φ' => !₂[-Real.cos θ * S 0 - Real.sin θ * S 1,
      Real.sin θ * Real.cos φ' * S 0 - Real.cos θ * Real.cos φ' * S 1]) := by
    ext φ' i; fin_cases i <;> simp [rotMθ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMθφ θ φ S = !₂[(0 : ℝ), -Real.sin θ * Real.sin φ * S 0 + Real.cos θ * Real.sin φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => Real.sin θ * Real.cos x * S 0) (-Real.sin θ * Real.sin φ * S 0) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (Real.sin θ)).mul_const (S 0)
      simp only [neg_mul, mul_neg, mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.cos θ * Real.cos x * S 1) (-Real.cos θ * Real.sin φ * S 1) φ := by
      have := ((Real.hasDerivAt_cos φ).const_mul (Real.cos θ)).mul_const (S 1)
      simp only [neg_mul, mul_neg, mul_assoc] at this ⊢; exact this
    convert h1.sub h2 using 1; ring

private lemma hasDerivAt_rotMφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMφ θ' φ S) (rotMθφ θ φ S) θ := by
  have h_f : (fun θ' => rotMφ θ' φ S) = (fun θ' => !₂[(0 : ℝ),
      Real.cos θ' * Real.sin φ * S 0 + Real.sin θ' * Real.sin φ * S 1 + Real.cos φ * S 2]) := by
    ext θ' i; fin_cases i <;> (simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  have h_f' : rotMθφ θ φ S = !₂[(0 : ℝ), -Real.sin θ * Real.sin φ * S 0 + Real.cos θ * Real.sin φ * S 1] := by
    ext i; fin_cases i <;> simp [rotMθφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail]
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => Real.cos x * Real.sin φ * S 0) (-Real.sin θ * Real.sin φ * S 0) θ := by
      have := (Real.hasDerivAt_cos θ).mul_const (Real.sin φ * S 0); simp only [mul_assoc, neg_mul] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin x * Real.sin φ * S 1) (Real.cos θ * Real.sin φ * S 1) θ := by
      have := (Real.hasDerivAt_sin θ).mul_const (Real.sin φ * S 1); simp only [mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun _ : ℝ => Real.cos φ * S 2) 0 θ := hasDerivAt_const _ _
    convert (h1.add h2).add h3 using 1; ring

private lemma hasDerivAt_rotMφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMφ θ φ' S) (rotMφφ θ φ S) φ := by
  have h_f : (fun φ' => rotMφ θ φ' S) = (fun φ' => !₂[(0 : ℝ),
      Real.cos θ * Real.sin φ' * S 0 + Real.sin θ * Real.sin φ' * S 1 + Real.cos φ' * S 2]) := by
    ext φ' i; fin_cases i <;> simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  have h_f' : rotMφφ θ φ S = !₂[(0 : ℝ),
      Real.cos θ * Real.cos φ * S 0 + Real.sin θ * Real.cos φ * S 1 - Real.sin φ * S 2] := by
    ext i; fin_cases i <;> simp [rotMφφ, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [h_f, h_f']; refine hasDerivAt_lp2 ?_ ?_
  · exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => Real.cos θ * Real.sin x * S 0) (Real.cos θ * Real.cos φ * S 0) φ := by
      have := ((Real.hasDerivAt_sin φ).const_mul (Real.cos θ)).mul_const (S 0)
      simp only [mul_assoc] at this ⊢; exact this
    have h2 : HasDerivAt (fun x => Real.sin θ * Real.sin x * S 1) (Real.sin θ * Real.cos φ * S 1) φ := by
      have := ((Real.hasDerivAt_sin φ).const_mul (Real.sin θ)).mul_const (S 1)
      simp only [mul_assoc] at this ⊢; exact this
    have h3 : HasDerivAt (fun x => Real.cos x * S 2) (-Real.sin φ * S 2) φ := by
      have := (Real.hasDerivAt_cos φ).mul_const (S 2); simp only [neg_mul] at this ⊢; exact this
    convert (h1.add h2).add h3 using 1; ring

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

-- Helper simp lemmas for rotR and rotR' applied to vectors
@[simp]
private lemma rotR_eq_toEuclideanLin (α : ℝ) :
    (rotR α : ℝ² →L[ℝ] ℝ²) = (rotR_mat α).toEuclideanLin.toContinuousLinearMap := rfl

@[simp]
private lemma rotR'_eq_toEuclideanLin (α : ℝ) :
    rotR' α = (rotR'_mat α).toEuclideanLin.toContinuousLinearMap := rfl

-- Explicit component lemmas for rotR applied to a vector
private lemma rotR_apply_0 (α : ℝ) (v : ℝ²) :
    (rotR α v) 0 = Real.cos α * v 0 - Real.sin α * v 1 := by
  simp [rotR, rotR_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotR_apply_1 (α : ℝ) (v : ℝ²) :
    (rotR α v) 1 = Real.sin α * v 0 + Real.cos α * v 1 := by
  simp [rotR, rotR_mat, Matrix.vecHead, Matrix.vecTail]

private lemma rotR'_apply_0 (α : ℝ) (v : ℝ²) :
    (rotR' α v) 0 = -Real.sin α * v 0 - Real.cos α * v 1 := by
  simp [rotR', rotR'_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotR'_apply_1 (α : ℝ) (v : ℝ²) :
    (rotR' α v) 1 = Real.cos α * v 0 - Real.sin α * v 1 := by
  simp [rotR', rotR'_mat, Matrix.vecHead, Matrix.vecTail]; ring

-- Explicit component lemmas for rotM applied to a vector
private lemma rotM_apply_0 (θ φ : ℝ) (S : ℝ³) :
    (rotM θ φ S) 0 = -Real.sin θ * S 0 + Real.cos θ * S 1 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]

private lemma rotM_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotM θ φ S) 1 = -Real.cos θ * Real.cos φ * S 0 - Real.sin θ * Real.cos φ * S 1 + Real.sin φ * S 2 := by
  simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_apply_0 (θ φ : ℝ) (S : ℝ³) :
    (rotMθ θ φ S) 0 = -Real.cos θ * S 0 - Real.sin θ * S 1 := by
  simp [rotMθ, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMθ_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotMθ θ φ S) 1 = Real.sin θ * Real.cos φ * S 0 - Real.cos θ * Real.cos φ * S 1 := by
  simp [rotMθ, Matrix.vecHead, Matrix.vecTail]; ring

private lemma rotMφ_apply_0 (θ φ : ℝ) (S : ℝ³) :
    (rotMφ θ φ S) 0 = 0 := by
  simp [rotMφ, Matrix.vecHead, Matrix.vecTail]

private lemma rotMφ_apply_1 (θ φ : ℝ) (S : ℝ³) :
    (rotMφ θ φ S) 1 = Real.cos θ * Real.sin φ * S 0 + Real.sin θ * Real.sin φ * S 1 + Real.cos φ * S 2 := by
  simp [rotMφ, Matrix.vecHead, Matrix.vecTail]; ring

-- Explicit computation of rotprojRM' applied to a vector (component 0)
private lemma rotprojRM'_apply_0 (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 0 =
      d 0 * (pbar.rotR' (pbar.rotM₁ S)) 0 +
      d 1 * (pbar.rotR (pbar.rotM₁θ S)) 0 +
      d 2 * (pbar.rotR (pbar.rotM₁φ S)) 0 := by
  simp only [rotprojRM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply]
  ring

-- Explicit computation of rotprojRM' applied to a vector (component 1)
private lemma rotprojRM'_apply_1 (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 1 =
      d 0 * (pbar.rotR' (pbar.rotM₁ S)) 1 +
      d 1 * (pbar.rotR (pbar.rotM₁θ S)) 1 +
      d 2 * (pbar.rotR (pbar.rotM₁φ S)) 1 := by
  simp only [rotprojRM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply]
  ring

-- Bridging lemma: function application equals .ofLp for EuclideanSpace
private lemma euclidean_ofLp_eq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    v i = v.ofLp i := rfl

-- Full expansion of rotprojRM'_apply_0 to arithmetic
private lemma rotprojRM'_apply_0_expanded (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 0 =
      d 0 * (-Real.sin pbar.α * (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) -
             Real.cos pbar.α * (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
                                 Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 + Real.sin pbar.φ₁ * S 2)) +
      d 1 * (Real.cos pbar.α * (-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) -
             Real.sin pbar.α * (Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1)) +
      d 2 * (Real.cos pbar.α * 0 -
             Real.sin pbar.α * (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
                                Real.cos pbar.φ₁ * S 2)) := by
  rw [rotprojRM'_apply_0]
  simp only [Pose.rotR', Pose.rotR, Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ]
  rw [rotR'_apply_0, rotR_apply_0, rotR_apply_0, rotM_apply_0, rotM_apply_1,
      rotMθ_apply_0, rotMθ_apply_1, rotMφ_apply_0, rotMφ_apply_1]

-- Full expansion of rotprojRM'_apply_1 to arithmetic
private lemma rotprojRM'_apply_1_expanded (pbar : Pose) (S : ℝ³) (d : ℝ³) :
    ((rotprojRM' pbar S) d) 1 =
      d 0 * (Real.cos pbar.α * (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) -
             Real.sin pbar.α * (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
                                 Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 + Real.sin pbar.φ₁ * S 2)) +
      d 1 * (Real.sin pbar.α * (-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) +
             Real.cos pbar.α * (Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1)) +
      d 2 * (Real.sin pbar.α * 0 +
             Real.cos pbar.α * (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
                                Real.cos pbar.φ₁ * S 2)) := by
  rw [rotprojRM'_apply_1]
  simp only [Pose.rotR', Pose.rotR, Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ]
  rw [rotR'_apply_1, rotR_apply_1, rotR_apply_1, rotM_apply_0, rotM_apply_1,
      rotMθ_apply_0, rotMθ_apply_1, rotMφ_apply_0, rotMφ_apply_1]

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

set_option maxHeartbeats 800000 in
lemma HasFDerivAt.rotproj_inner (pbar : Pose) (S : ℝ³) (w : ℝ²) :
    (HasFDerivAt (rotproj_inner S w) (rotproj_inner' pbar S w) pbar.innerParams) := by

  have z1 : HasFDerivAt (fun x => (rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S) (rotprojRM' pbar S) pbar.innerParams := by
    -- The function is f(α, θ, φ) = rotR α (rotM θ φ S)
    -- Prove via component-wise HasStrictFDerivAt
    apply HasStrictFDerivAt.hasFDerivAt
    rw [hasStrictFDerivAt_piLp]
    intro i
    -- Define projections for coordinates
    let proj0 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
    let proj1 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)
    let proj2 : ℝ³ →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
    have hproj0 : HasStrictFDerivAt (fun x : ℝ³ => x.ofLp 0) proj0 pbar.innerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.innerParams 0
    have hproj1 : HasStrictFDerivAt (fun x : ℝ³ => x.ofLp 1) proj1 pbar.innerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.innerParams 1
    have hproj2 : HasStrictFDerivAt (fun x : ℝ³ => x.ofLp 2) proj2 pbar.innerParams :=
      PiLp.hasStrictFDerivAt_apply 2 pbar.innerParams 2
    have hα : pbar.innerParams.ofLp 0 = pbar.α := by simp [Pose.innerParams]
    have hθ : pbar.innerParams.ofLp 1 = pbar.θ₁ := by simp [Pose.innerParams]
    have hφ : pbar.innerParams.ofLp 2 = pbar.φ₁ := by simp [Pose.innerParams]
    have hsinα : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 0))
        (Real.cos pbar.α • proj0) pbar.innerParams :=
      (Real.hasStrictDerivAt_sin pbar.α).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj0 hα.symm
    have hcosα : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 0))
        (-(Real.sin pbar.α) • proj0) pbar.innerParams :=
      (Real.hasStrictDerivAt_cos pbar.α).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj0 hα.symm
    have hsinθ : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 1))
        (Real.cos pbar.θ₁ • proj1) pbar.innerParams :=
      (Real.hasStrictDerivAt_sin pbar.θ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj1 hθ.symm
    have hcosθ : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 1))
        (-(Real.sin pbar.θ₁) • proj1) pbar.innerParams :=
      (Real.hasStrictDerivAt_cos pbar.θ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj1 hθ.symm
    have hsinφ : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 2))
        (Real.cos pbar.φ₁ • proj2) pbar.innerParams :=
      (Real.hasStrictDerivAt_sin pbar.φ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj2 hφ.symm
    have hcosφ : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 2))
        (-(Real.sin pbar.φ₁) • proj2) pbar.innerParams :=
      (Real.hasStrictDerivAt_cos pbar.φ₁).comp_hasStrictFDerivAt_of_eq pbar.innerParams hproj2 hφ.symm
    -- Helper lemmas for product terms
    have hA : HasStrictFDerivAt (fun x : ℝ³ => -Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1)
        ((-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) • proj1) pbar.innerParams := by
      have h1 := hsinθ.neg.mul_const (S 0)
      have h2 := hcosθ.mul_const (S 1)
      convert h1.add h2 using 1 <;> ext d <;>
        simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
    have hcosθcosφ : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2))
        (Real.cos pbar.θ₁ • (-(Real.sin pbar.φ₁) • proj2) + Real.cos pbar.φ₁ • (-(Real.sin pbar.θ₁) • proj1))
        pbar.innerParams := hcosθ.mul hcosφ
    have hsinθcosφ : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2))
        (Real.sin pbar.θ₁ • (-(Real.sin pbar.φ₁) • proj2) + Real.cos pbar.φ₁ • (Real.cos pbar.θ₁ • proj1))
        pbar.innerParams := hsinθ.mul hcosφ
    have hB : HasStrictFDerivAt (fun x : ℝ³ => -Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
          Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2)
        ((Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1) • proj1 +
         (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
          Real.cos pbar.φ₁ * S 2) • proj2) pbar.innerParams := by
      have h1 := hcosθcosφ.neg.mul_const (S 0)
      have h2 := hsinθcosφ.mul_const (S 1)
      have h3 := hsinφ.mul_const (S 2)
      convert (h1.sub h2).add h3 using 1 <;> ext d <;>
        simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
              ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul] <;> ring
    fin_cases i
    · -- Component 0: cos(α) * A - sin(α) * B
      simp only [Fin.isValue, show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl]
      have hfunc : (fun x : ℝ³ => ((rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S).ofLp (0 : Fin 2)) =
          fun x => Real.cos (x.ofLp 0) * (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1) -
                   Real.sin (x.ofLp 0) * (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
                     Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2) := by
        ext x
        have := rotprojRM_component0 (x.ofLp 1) (x.ofLp 2) (x.ofLp 0) S
        simp only [rotprojRM, ContinuousLinearMap.coe_comp', Function.comp_apply] at this ⊢
        exact this
      rw [hfunc]
      have hcosA : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 0) *
            (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1))
          (Real.cos pbar.α • ((-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) • proj1) +
           (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) • (-(Real.sin pbar.α) • proj0))
          pbar.innerParams := hcosα.mul hA
      have hsinB : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 0) *
            (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
             Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2))
          (Real.sin pbar.α • ((Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
               Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1) • proj1 +
             (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
              Real.cos pbar.φ₁ * S 2) • proj2) +
           (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 +
            Real.sin pbar.φ₁ * S 2) • (Real.cos pbar.α • proj0))
          pbar.innerParams := hsinα.mul hB
      have hfinal := hcosA.sub hsinB
      refine HasStrictFDerivAt.congr_fderiv hfinal ?_
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show ((rotprojRM' pbar S) d).ofLp 0 = ((rotprojRM' pbar S) d) 0 from rfl]
      rw [rotprojRM'_apply_0_expanded]
      simp only [show proj0 d = d.ofLp 0 from rfl, show proj1 d = d.ofLp 1 from rfl,
                 show proj2 d = d.ofLp 2 from rfl, mul_zero, zero_sub]
      ring
    · -- Component 1: sin(α) * A + cos(α) * B
      simp only [Fin.isValue, show (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) from rfl]
      have hfunc : (fun x : ℝ³ => ((rotprojRM (x.ofLp 1) (x.ofLp 2) (x.ofLp 0)) S).ofLp (1 : Fin 2)) =
          fun x => Real.sin (x.ofLp 0) * (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1) +
                   Real.cos (x.ofLp 0) * (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
                     Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2) := by
        ext x
        have := rotprojRM_component1 (x.ofLp 1) (x.ofLp 2) (x.ofLp 0) S
        simp only [rotprojRM, ContinuousLinearMap.coe_comp', Function.comp_apply] at this ⊢
        exact this
      rw [hfunc]
      have hsinA : HasStrictFDerivAt (fun x : ℝ³ => Real.sin (x.ofLp 0) *
            (-Real.sin (x.ofLp 1) * S 0 + Real.cos (x.ofLp 1) * S 1))
          (Real.sin pbar.α • ((-Real.cos pbar.θ₁ * S 0 - Real.sin pbar.θ₁ * S 1) • proj1) +
           (-Real.sin pbar.θ₁ * S 0 + Real.cos pbar.θ₁ * S 1) • (Real.cos pbar.α • proj0))
          pbar.innerParams := hsinα.mul hA
      have hcosB : HasStrictFDerivAt (fun x : ℝ³ => Real.cos (x.ofLp 0) *
            (-Real.cos (x.ofLp 1) * Real.cos (x.ofLp 2) * S 0 -
             Real.sin (x.ofLp 1) * Real.cos (x.ofLp 2) * S 1 + Real.sin (x.ofLp 2) * S 2))
          (Real.cos pbar.α • ((Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 0 -
               Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 1) • proj1 +
             (Real.cos pbar.θ₁ * Real.sin pbar.φ₁ * S 0 + Real.sin pbar.θ₁ * Real.sin pbar.φ₁ * S 1 +
              Real.cos pbar.φ₁ * S 2) • proj2) +
           (-Real.cos pbar.θ₁ * Real.cos pbar.φ₁ * S 0 - Real.sin pbar.θ₁ * Real.cos pbar.φ₁ * S 1 +
            Real.sin pbar.φ₁ * S 2) • (-(Real.sin pbar.α) • proj0))
          pbar.innerParams := hcosα.mul hB
      have hfinal := hsinA.add hcosB
      refine HasStrictFDerivAt.congr_fderiv hfinal ?_
      ext d
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, PiLp.proj_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show ((rotprojRM' pbar S) d).ofLp 1 = ((rotprojRM' pbar S) d) 1 from rfl]
      rw [rotprojRM'_apply_1_expanded]
      simp only [show proj0 d = d.ofLp 0 from rfl, show proj1 d = d.ofLp 1 from rfl,
                 show proj2 d = d.ofLp 2 from rfl, mul_zero, zero_add]
      ring

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

-- The second partial derivatives of the inner-rotM function
-- Each equals ⟪A S, w⟫ where A ∈ {rotMθθ, rotMθφ, rotMφφ}
-- These follow from differentiating rotM twice using hasDerivAt_rotMθ_θ etc.
private lemma second_partial_inner_rotM_outer (S : ℝ³) (w : ℝ²) (x : E 2) (i j : Fin 2) :
    ∃ A : ℝ³ →L[ℝ] ℝ², ‖A‖ ≤ 1 ∧
      nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x = ⟪A S, w⟫ := by
  -- Each pair (i, j) corresponds to a specific second derivative matrix
  -- (0, 0) → rotMθθ, (0, 1) → rotMθφ, (1, 0) → rotMθφ, (1, 1) → rotMφφ
  -- All have operator norm ≤ 1 by rotMθθ_norm_le_one, rotMθφ_norm_le_one, rotMφφ_norm_le_one
  fin_cases i <;> fin_cases j
  · -- (0, 0): uses rotMθθ
    refine ⟨rotMθθ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθθ_norm_le_one _ _, ?_⟩
    simp only [nth_partial]
    -- The second partial of ⟪rotM S, w⟫ w.r.t. (θ, θ) equals ⟪rotMθθ S, w⟫
    -- Proof strategy:
    -- 1. First partial ∂/∂θ gives inner product with rotMθ (via fderiv_inner_apply + rotM')
    -- 2. Second partial ∂/∂θ gives inner product with rotMθθ (via hasDerivAt_rotMθ_θ)
    let θ := x.ofLp 0; let φ := x.ofLp 1
    let e₀ : E 2 := EuclideanSpace.single 0 1
    have hDiff : Differentiable ℝ fun y : E 2 => (rotM (y.ofLp 0) (y.ofLp 1)) S :=
      Differentiable.rotM_outer S
    -- Helper: fderiv of rotM applied to e₀ gives rotMθ
    have hfderiv_rotM : ∀ y : E 2, fderiv ℝ (fun z : E 2 => (rotM (z.ofLp 0) (z.ofLp 1)) S) y e₀ =
        rotMθ (y.ofLp 0) (y.ofLp 1) S := by
      intro y
      -- Use HasFDerivAt.rotM_outer with a pose whose outerParams = y
      let pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩
      have hpbar_eq : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hrotM : HasFDerivAt (fun z => (rotM (z.ofLp 0) (z.ofLp 1)) S) (rotM' pbar S) y := by
        convert HasFDerivAt.rotM_outer pbar S using 2; exact hpbar_eq.symm
      rw [hrotM.fderiv]
      -- rotM' pbar S applied to e₀ = rotMθ
      -- pbar.θ₂ = y.ofLp 0 and pbar.φ₂ = y.ofLp 1 by definition of pbar
      -- e₀ = EuclideanSpace.single 0 1 means (e₀.ofLp 0, e₀.ofLp 1) = (1, 0)
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      -- The goal: matrix with columns [rotMθ, rotMφ] applied to e₀=(1,0) = rotMθ
      -- pbar.θ₂ = y.ofLp 0, pbar.φ₂ = y.ofLp 1 definitionally
      -- e₀ = (1, 0), so first column gets picked
      have he0_0 : e₀.ofLp 0 = 1 := rfl
      have he0_1 : e₀.ofLp 1 = 0 := by
        show (EuclideanSpace.single 0 1 : E 2).ofLp 1 = 0
        simp only [EuclideanSpace.single_apply, show (1 : Fin 2) ≠ 0 from by decide, if_false]
      ext i; fin_cases i <;>
        (simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.of_apply, he0_0, he0_1, mul_one, mul_zero, add_zero]; rfl)
    -- Function equality: the first partial equals inner product with rotMθ
    have hfunc_eq : (fun y => (fderiv ℝ (fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y) e₀) =
        fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      ext y
      have hInner := fderiv_inner_apply ℝ (hDiff y) (by fun_prop : DifferentiableAt ℝ (fun _ => w) y) e₀
      rw [hInner, hfderiv_rotM y]
      -- Goal: ⟪rotM S, (fderiv (const w)) e₀⟫ + ⟪rotMθ S, w⟫ = ⟪rotMθ S, w⟫
      -- The fderiv of constant function w is 0
      have h0 : (fderiv ℝ (fun _ : E 2 => w) y) e₀ = 0 := by
        rw [show (fun _ : E 2 => w) = Function.const (E 2) w from rfl, fderiv_const]
        simp
      simp only [h0, inner_zero_right, zero_add]
    -- Need to unfold nth_partial in the goal to use hfunc_eq
    -- nth_partial i f = fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)
    unfold nth_partial
    -- Goal: (fderiv (fun y => (fderiv inner) e₀) x) e₀ = ...
    -- The inner function is the same as in hfunc_eq (e₀ = EuclideanSpace.single 0 1)
    have h_eq : (fun x_1 => (fderiv ℝ (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) x_1)
        (EuclideanSpace.single 0 1)) = (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) := hfunc_eq
    rw [h_eq]
    -- Now differentiate ⟪rotMθ S, w⟫ w.r.t. θ (direction e₀)
    have hDiff2 : Differentiable ℝ fun y : E 2 => rotMθ (y.ofLp 0) (y.ofLp 1) S := by
      rw [differentiable_piLp]; intro i; fin_cases i
      · simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons]; fun_prop
      · simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons]; fun_prop
    have hInner2 := fderiv_inner_apply ℝ (hDiff2 x) (by fun_prop : DifferentiableAt ℝ (fun _ => w) x)
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
      inner_zero_right, add_zero] at hInner2
    rw [hInner2]
    -- fderiv of rotMθ at x applied to e₀ = rotMθθ
    -- Use hasDerivAt_rotMθ_θ: HasDerivAt (fun θ' => rotMθ θ' φ S) (rotMθθ θ φ S) θ
    have hderiv := hasDerivAt_rotMθ_θ θ φ S
    have hfderiv : fderiv ℝ (fun y : E 2 => rotMθ (y.ofLp 0) (y.ofLp 1) S) x e₀ = rotMθθ θ φ S := by
      -- The derivative only involves the θ component (index 0)
      have hcomp : (fun y : E 2 => rotMθ (y.ofLp 0) (y.ofLp 1) S) =
          (fun θ' => rotMθ θ' φ S) ∘ (fun y : E 2 => y.ofLp 0) := by ext y; rfl
      rw [hcomp]
      rw [fderiv.comp x hderiv.differentiableAt (PiLp.differentiableAt_apply 2 x 0)]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
      rw [PiLp.fderiv_apply 2 x 0, hderiv.fderiv]
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
        PiLp.proj_apply, EuclideanSpace.single_apply, ↓reduceIte, smul_eq_mul, mul_one]
    rw [hfderiv]
  · -- (0, 1): uses rotMθφ (derivative of rotMφ w.r.t. θ)
    -- This case is symmetric to (0,0) but uses hasDerivAt_rotMφ_θ instead of hasDerivAt_rotMθ_θ
    refine ⟨rotMθφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθφ_norm_le_one _ _, ?_⟩
    simp only [nth_partial]
    let θ := x.ofLp 0; let φ := x.ofLp 1
    let e₀ : E 2 := EuclideanSpace.single 0 1
    let e₁ : E 2 := EuclideanSpace.single 1 1
    have hDiff : Differentiable ℝ fun y : E 2 => (rotM (y.ofLp 0) (y.ofLp 1)) S :=
      Differentiable.rotM_outer S
    -- First partial: fderiv of ⟪rotM S, w⟫ applied to e₁ gives ⟪rotMφ S, w⟫
    have hfderiv_rotM : ∀ y : E 2, fderiv ℝ (fun z : E 2 => (rotM (z.ofLp 0) (z.ofLp 1)) S) y e₁ =
        rotMφ (y.ofLp 0) (y.ofLp 1) S := by
      intro y
      let pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩
      have hpbar_eq : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hrotM : HasFDerivAt (fun z => (rotM (z.ofLp 0) (z.ofLp 1)) S) (rotM' pbar S) y := by
        convert HasFDerivAt.rotM_outer pbar S using 2; exact hpbar_eq.symm
      rw [hrotM.fderiv]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      have he1_0 : e₁.ofLp 0 = 0 := by
        show (EuclideanSpace.single 1 1 : E 2).ofLp 0 = 0
        simp only [EuclideanSpace.single_apply, show (0 : Fin 2) ≠ 1 from by decide, if_false]
      have he1_1 : e₁.ofLp 1 = 1 := rfl
      ext i; fin_cases i <;>
        (simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.of_apply, he1_0, he1_1, mul_one, mul_zero, zero_add]; rfl)
    have hfunc_eq : (fun y => (fderiv ℝ (fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y) e₁) =
        fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      ext y
      have hInner := fderiv_inner_apply ℝ (hDiff y) (by fun_prop : DifferentiableAt ℝ (fun _ => w) y) e₁
      rw [hInner, hfderiv_rotM y]
      have h0 : (fderiv ℝ (fun _ : E 2 => w) y) e₁ = 0 := by
        rw [show (fun _ : E 2 => w) = Function.const (E 2) w from rfl, fderiv_const]; simp
      simp only [h0, inner_zero_right, zero_add]
    -- Use change to match e₁ with the syntactic form in the goal
    change (fderiv ℝ (fun x => (fderiv ℝ (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) x) e₁) x) e₀ =
        ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫
    have step1 : fderiv ℝ (fun x => (fderiv ℝ (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) x) e₁) =
        fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) := congrArg (fderiv ℝ) hfunc_eq
    rw [step1]
    -- Second partial: differentiate ⟪rotMφ S, w⟫ w.r.t. θ (direction e₀)
    have hDiff2 : Differentiable ℝ fun y : E 2 => rotMφ (y.ofLp 0) (y.ofLp 1) S := by
      intro y; rw [differentiableAt_piLp]; intro i; fin_cases i
      · simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons]; fun_prop
      · simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons]; fun_prop
    have hInner2 := fderiv_inner_apply ℝ (hDiff2 x) (by fun_prop : DifferentiableAt ℝ (fun _ => w) x)
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
      inner_zero_right, add_zero] at hInner2
    rw [hInner2]
    -- fderiv of rotMφ at x applied to e₀ = rotMθφ using hasDerivAt_rotMφ_θ
    have hderiv := hasDerivAt_rotMφ_θ θ φ S
    have hfderiv : fderiv ℝ (fun y : E 2 => rotMφ (y.ofLp 0) (y.ofLp 1) S) x e₀ = rotMθφ θ φ S := by
      -- Key: the function (y ↦ rotMφ (y 0) (y 1) S) composed with projection onto first coord
      -- gives the same θ-derivative as (θ' ↦ rotMφ θ' φ S) at θ
      -- This works because the first component of fderiv extracts the θ-partial derivative
      have hcomp : (fun y : E 2 => rotMφ (y.ofLp 0) (y.ofLp 1) S) =
          (fun p : ℝ × ℝ => rotMφ p.1 p.2 S) ∘ (fun y : E 2 => (y.ofLp 0, y.ofLp 1)) := rfl
      -- At x, the fderiv gives a linear map, and e₀ extracts just the ∂/∂θ component
      -- Since rotMφ θ φ S is linear in (θ, φ) in a smooth way, chain rule applies
      -- The derivative of (θ', φ') ↦ rotMφ θ' φ' S is (dθ, dφ) ↦ rotMθφ θ φ S * dθ + rotMφφ θ φ S * dφ
      -- Applying to (1, 0) = (e₀.ofLp 0, e₀.ofLp 1) gives rotMθφ θ φ S
      -- Use explicit component-wise computation
      ext i; fin_cases i
      · -- First component
        simp only [rotMφ, rotMθφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Fin.isValue]
        -- The first component of rotMφ is always 0, so its derivative is 0
        -- The first component of rotMθφ is also 0
        have h_comp0 : ∀ y : E 2, (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 0 = 0 := by
          intro y; simp [rotMφ, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        have hconst0 : (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 0) = fun _ => (0 : ℝ) := by
          ext y; exact h_comp0 y
        have heq0 : (fderiv ℝ (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 0) x) e₀ =
            (fderiv ℝ (fun _ : E 2 => (0 : ℝ)) x) e₀ := by
          congr 2; exact hconst0
        rw [heq0]; simp [fderiv_const]
      · -- Second component
        simp only [rotMφ, rotMθφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Fin.isValue]
        -- Second component of rotMφ θ φ S is cos θ * sin φ * S₀ + sin θ * sin φ * S₁ + cos φ * S₂
        -- Its derivative w.r.t. θ is -sin θ * sin φ * S₀ + cos θ * sin φ * S₁
        -- This equals the second component of rotMθφ θ φ S
        have h_comp1 : (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 1) =
            fun y => Real.cos (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 0 +
                     Real.sin (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 1 +
                     Real.cos (y.ofLp 1) * S.ofLp 2 := by
          ext y; simp [rotMφ, Matrix.toEuclideanLin_apply, dotProduct, Fin.sum_univ_three]
        have heq : (fderiv ℝ (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 1) x) e₀ =
            (fderiv ℝ (fun y => Real.cos (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 0 +
                     Real.sin (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 1 +
                     Real.cos (y.ofLp 1) * S.ofLp 2) x) e₀ := by
          congr 2; exact h_comp1
        rw [heq]
        -- Now compute the derivative of this explicit expression
        have hd : HasFDerivAt (fun y : E 2 => Real.cos (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 0 +
                     Real.sin (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 1 +
                     Real.cos (y.ofLp 1) * S.ofLp 2) _ x := by fun_prop
        rw [hd.fderiv]
        -- The e₀-component extracts the θ-derivative
        simp only [EuclideanSpace.single_apply, ↓reduceIte]
        -- This should equal -sin θ * sin φ * S₀ + cos θ * sin φ * S₁
        simp only [rotMθφ, Matrix.of_apply, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
          mul_zero, add_zero]
        ring
    rw [hfderiv]
    -- Now simplify: fderiv of constant w is 0, and θ = x.ofLp 0, φ = x.ofLp 1
    have hconst : (fderiv ℝ (fun _ : E 2 => w) x) e₀ = 0 := by
      rw [show (fun _ : E 2 => w) = Function.const (E 2) w from rfl, fderiv_const]; simp
    simp only [hconst, inner_zero_right, zero_add]
    -- θ = x.ofLp 0 and φ = x.ofLp 1 by let-binding, so the goal is defeq
    rfl
  · -- (1, 0): uses rotMθφ (derivative of rotMθ w.r.t. φ)
    -- First partial w.r.t. j=0 (θ) gives rotMθ
    -- Second partial w.r.t. i=1 (φ) gives rotMθφ via hasDerivAt_rotMθ_φ
    refine ⟨rotMθφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMθφ_norm_le_one _ _, ?_⟩
    simp only [nth_partial]
    let θ := x.ofLp 0; let φ := x.ofLp 1
    let e₀ : E 2 := EuclideanSpace.single 0 1
    let e₁ : E 2 := EuclideanSpace.single 1 1
    have hDiff : Differentiable ℝ fun y : E 2 => (rotM (y.ofLp 0) (y.ofLp 1)) S :=
      Differentiable.rotM_outer S
    -- First partial: fderiv of ⟪rotM S, w⟫ applied to e₀ gives ⟪rotMθ S, w⟫
    have hfderiv_rotM : ∀ y : E 2, fderiv ℝ (fun z : E 2 => (rotM (z.ofLp 0) (z.ofLp 1)) S) y e₀ =
        rotMθ (y.ofLp 0) (y.ofLp 1) S := by
      intro y
      let pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩
      have hpbar_eq : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hrotM : HasFDerivAt (fun z => (rotM (z.ofLp 0) (z.ofLp 1)) S) (rotM' pbar S) y := by
        convert HasFDerivAt.rotM_outer pbar S using 2; exact hpbar_eq.symm
      rw [hrotM.fderiv]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      have he0_0 : e₀.ofLp 0 = 1 := rfl
      have he0_1 : e₀.ofLp 1 = 0 := by
        show (EuclideanSpace.single 0 1 : E 2).ofLp 1 = 0
        simp only [EuclideanSpace.single_apply, show (1 : Fin 2) ≠ 0 from by decide, if_false]
      ext i; fin_cases i <;>
        (simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.of_apply, he0_0, he0_1, mul_one, mul_zero, add_zero]; rfl)
    have hfunc_eq : (fun y => (fderiv ℝ (fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y) e₀) =
        fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      ext y
      have hInner := fderiv_inner_apply ℝ (hDiff y) (by fun_prop : DifferentiableAt ℝ (fun _ => w) y) e₀
      rw [hInner, hfderiv_rotM y]
      have h0 : (fderiv ℝ (fun _ : E 2 => w) y) e₀ = 0 := by
        rw [show (fun _ : E 2 => w) = Function.const (E 2) w from rfl, fderiv_const]; simp
      simp only [h0, inner_zero_right, zero_add]
    -- Use change to match e₀ with the syntactic form in the goal
    change (fderiv ℝ (fun x => (fderiv ℝ (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) x) e₀) x) e₁ =
        ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫
    have step1 : fderiv ℝ (fun x => (fderiv ℝ (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) x) e₀) =
        fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) := congrArg (fderiv ℝ) hfunc_eq
    rw [step1]
    -- Second partial: differentiate ⟪rotMθ S, w⟫ w.r.t. φ (direction e₁)
    have hDiff2 : Differentiable ℝ fun y : E 2 => rotMθ (y.ofLp 0) (y.ofLp 1) S := by
      intro y; rw [differentiableAt_piLp]; intro i; fin_cases i
      · -- Component 0: -cos(θ) * S₀ - sin(θ) * S₁ + 0 * S₂
        simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        -- The matrix lookups are definitionally equal to scalars, show that to fun_prop
        show DifferentiableAt ℝ (fun x : E 2 => -Real.cos (x.ofLp 0) * S.ofLp 0 +
            (-Real.sin (x.ofLp 0)) * S.ofLp 1 + 0 * S.ofLp 2) y
        fun_prop
      · -- Component 1: sin(θ) * cos(φ) * S₀ + (-cos(θ) * cos(φ)) * S₁ + 0 * S₂
        simp only [rotMθ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        -- Row 1 of the matrix: [sin θ * cos φ, -cos θ * cos φ, 0]
        -- Note: matrix has -cos θ * cos φ, NOT -(cos θ * cos φ)
        show DifferentiableAt ℝ (fun x : E 2 =>
            (Real.sin (x.ofLp 0) * Real.cos (x.ofLp 1)) * S.ofLp 0 +
            (-Real.cos (x.ofLp 0) * Real.cos (x.ofLp 1)) * S.ofLp 1 +
            0 * S.ofLp 2) y
        fun_prop
    have hInner2 := fderiv_inner_apply ℝ (hDiff2 x) (by fun_prop : DifferentiableAt ℝ (fun _ => w) x)
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
      inner_zero_right, add_zero] at hInner2
    rw [hInner2]
    -- fderiv of rotMθ at x applied to e₁ = rotMθφ using hasDerivAt_rotMθ_φ
    have hderiv := hasDerivAt_rotMθ_φ θ φ S
    have hfderiv : fderiv ℝ (fun y : E 2 => rotMθ (y.ofLp 0) (y.ofLp 1) S) x e₁ = rotMθφ θ φ S := by
      -- The directional derivative in direction e₁ = (0,1) equals the partial w.r.t. φ
      -- Component 0 of rotMθ doesn't depend on φ, so derivative is 0
      -- Component 1 derivative uses hasDerivAt_rotMθ_φ
      ext i; fin_cases i
      · -- First component: -cos θ * S₀ - sin θ * S₁ + 0 * S₂ doesn't depend on φ
        simp only [rotMθ, rotMθφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue]
        have h_comp0 : (fun y : E 2 => (rotMθ (y.ofLp 0) (y.ofLp 1) S).ofLp 0) =
            fun y => -Real.cos (y.ofLp 0) * S.ofLp 0 + (-Real.sin (y.ofLp 0)) * S.ofLp 1 := by
          ext y; simp [rotMθ, Matrix.toEuclideanLin_apply, dotProduct, Fin.sum_univ_three]
        have heq : (fderiv ℝ (fun y : E 2 => (rotMθ (y.ofLp 0) (y.ofLp 1) S).ofLp 0) x) e₁ =
            (fderiv ℝ (fun y => -Real.cos (y.ofLp 0) * S.ofLp 0 + (-Real.sin (y.ofLp 0)) * S.ofLp 1) x) e₁ := by
          congr 2; exact h_comp0
        rw [heq]
        -- Derivative of -cos θ * S₀ - sin θ * S₁ w.r.t. φ (direction e₁) is 0
        have hd : HasFDerivAt (fun y : E 2 => -Real.cos (y.ofLp 0) * S.ofLp 0 + (-Real.sin (y.ofLp 0)) * S.ofLp 1) _ x := by fun_prop
        rw [hd.fderiv]; simp only [EuclideanSpace.single_apply, ↓reduceIte, Fin.one_eq_zero_iff,
          mul_zero, add_zero]
      · -- Second component: sin θ * cos φ * S₀ - cos θ * cos φ * S₁
        -- Derivative w.r.t. φ is -sin θ * sin φ * S₀ + cos θ * sin φ * S₁
        simp only [rotMθ, rotMθφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue]
        have h_comp1 : (fun y : E 2 => (rotMθ (y.ofLp 0) (y.ofLp 1) S).ofLp 1) =
            fun y => Real.sin (y.ofLp 0) * Real.cos (y.ofLp 1) * S.ofLp 0 +
                     (-Real.cos (y.ofLp 0) * Real.cos (y.ofLp 1)) * S.ofLp 1 := by
          ext y; simp [rotMθ, Matrix.toEuclideanLin_apply, dotProduct, Fin.sum_univ_three]; ring
        have heq : (fderiv ℝ (fun y : E 2 => (rotMθ (y.ofLp 0) (y.ofLp 1) S).ofLp 1) x) e₁ =
            (fderiv ℝ (fun y => Real.sin (y.ofLp 0) * Real.cos (y.ofLp 1) * S.ofLp 0 +
                     (-Real.cos (y.ofLp 0) * Real.cos (y.ofLp 1)) * S.ofLp 1) x) e₁ := by
          congr 2; exact h_comp1
        rw [heq]
        have hd : HasFDerivAt (fun y : E 2 => Real.sin (y.ofLp 0) * Real.cos (y.ofLp 1) * S.ofLp 0 +
                     (-Real.cos (y.ofLp 0) * Real.cos (y.ofLp 1)) * S.ofLp 1) _ x := by fun_prop
        rw [hd.fderiv]; simp only [EuclideanSpace.single_apply, ↓reduceIte, Fin.zero_eq_one_iff,
          mul_one, mul_zero, add_zero]
        simp only [rotMθφ, Matrix.of_apply, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
          mul_zero, add_zero]
        ring
    rw [hfderiv]
    -- Simplify: fderiv of constant w is 0, and θ = x.ofLp 0, φ = x.ofLp 1
    have hconst : (fderiv ℝ (fun _ : E 2 => w) x) e₁ = 0 := by
      rw [show (fun _ : E 2 => w) = Function.const (E 2) w from rfl, fderiv_const]; simp
    simp only [hconst, inner_zero_right, zero_add]
    rfl
  · -- (1, 1): uses rotMφφ (derivative of rotMφ w.r.t. φ)
    -- First partial w.r.t. j=1 (φ) gives rotMφ
    -- Second partial w.r.t. i=1 (φ) gives rotMφφ via hasDerivAt_rotMφ_φ
    refine ⟨rotMφφ (x.ofLp 0) (x.ofLp 1), Bounding.rotMφφ_norm_le_one _ _, ?_⟩
    simp only [nth_partial]
    let θ := x.ofLp 0; let φ := x.ofLp 1
    let e₁ : E 2 := EuclideanSpace.single 1 1
    have hDiff : Differentiable ℝ fun y : E 2 => (rotM (y.ofLp 0) (y.ofLp 1)) S :=
      Differentiable.rotM_outer S
    -- First partial: fderiv of ⟪rotM S, w⟫ applied to e₁ gives ⟪rotMφ S, w⟫
    have hfderiv_rotM : ∀ y : E 2, fderiv ℝ (fun z : E 2 => (rotM (z.ofLp 0) (z.ofLp 1)) S) y e₁ =
        rotMφ (y.ofLp 0) (y.ofLp 1) S := by
      intro y
      let pbar : Pose := ⟨0, y.ofLp 0, 0, y.ofLp 1, 0⟩
      have hpbar_eq : pbar.outerParams = y := by ext i; fin_cases i <;> rfl
      have hrotM : HasFDerivAt (fun z => (rotM (z.ofLp 0) (z.ofLp 1)) S) (rotM' pbar S) y := by
        convert HasFDerivAt.rotM_outer pbar S using 2; exact hpbar_eq.symm
      rw [hrotM.fderiv]
      simp only [rotM', LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
      have he1_0 : e₁.ofLp 0 = 0 := by
        show (EuclideanSpace.single 1 1 : E 2).ofLp 0 = 0
        simp only [EuclideanSpace.single_apply, show (0 : Fin 2) ≠ 1 from by decide, if_false]
      have he1_1 : e₁.ofLp 1 = 1 := rfl
      ext i; fin_cases i <;>
        (simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.of_apply, he1_0, he1_1, mul_one, mul_zero, zero_add]; rfl)
    have hfunc_eq : (fun y => (fderiv ℝ (fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y) e₁) =
        fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
      ext y
      have hInner := fderiv_inner_apply ℝ (hDiff y) (by fun_prop : DifferentiableAt ℝ (fun _ => w) y) e₁
      rw [hInner, hfderiv_rotM y]
      have h0 : (fderiv ℝ (fun _ : E 2 => w) y) e₁ = 0 := by
        rw [show (fun _ : E 2 => w) = Function.const (E 2) w from rfl, fderiv_const]; simp
      simp only [h0, inner_zero_right, zero_add]
    -- Use change to match e₁ with the syntactic form in the goal
    change (fderiv ℝ (fun x => (fderiv ℝ (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) x) e₁) x) e₁ =
        ⟪rotMφφ (x.ofLp 0) (x.ofLp 1) S, w⟫
    have step1 : fderiv ℝ (fun x => (fderiv ℝ (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) x) e₁) =
        fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) := congrArg (fderiv ℝ) hfunc_eq
    rw [step1]
    -- Second partial: differentiate ⟪rotMφ S, w⟫ w.r.t. φ (direction e₁)
    have hDiff2 : Differentiable ℝ fun y : E 2 => rotMφ (y.ofLp 0) (y.ofLp 1) S := by
      intro y; rw [differentiableAt_piLp]; intro i; fin_cases i
      · -- Component 0: always 0 (first row is [0, 0, 0])
        simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        show DifferentiableAt ℝ (fun _ : E 2 => (0 : ℝ) * S.ofLp 0 + 0 * S.ofLp 1 + 0 * S.ofLp 2) y
        fun_prop
      · -- Component 1: cos(θ)*sin(φ)*S₀ + sin(θ)*sin(φ)*S₁ + cos(φ)*S₂
        simp only [rotMφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        show DifferentiableAt ℝ (fun x : E 2 =>
            (Real.cos (x.ofLp 0) * Real.sin (x.ofLp 1)) * S.ofLp 0 +
            (Real.sin (x.ofLp 0) * Real.sin (x.ofLp 1)) * S.ofLp 1 +
            (Real.cos (x.ofLp 1)) * S.ofLp 2) y
        fun_prop
    have hInner2 := fderiv_inner_apply ℝ (hDiff2 x) (by fun_prop : DifferentiableAt ℝ (fun _ => w) x)
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
      inner_zero_right, add_zero] at hInner2
    rw [hInner2]
    -- fderiv of rotMφ at x applied to e₁ = rotMφφ using hasDerivAt_rotMφ_φ
    have hderiv := hasDerivAt_rotMφ_φ θ φ S
    have hfderiv : fderiv ℝ (fun y : E 2 => rotMφ (y.ofLp 0) (y.ofLp 1) S) x e₁ = rotMφφ θ φ S := by
      -- The directional derivative in direction e₁ = (0,1) equals the partial w.r.t. φ
      -- Component 0 of rotMφ is always 0 (first row is [0, 0, 0])
      -- Component 1 derivative uses the φ-derivative of sin φ → cos φ and cos φ → -sin φ
      ext i; fin_cases i
      · -- First component: 0 (constant), derivative is 0
        simp only [rotMφ, rotMφφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue]
        have h_comp0 : (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 0) =
            fun _ => (0 : ℝ) := by
          ext y; simp [rotMφ, Matrix.toEuclideanLin_apply, dotProduct, Fin.sum_univ_three,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        have hconst0 : (fderiv ℝ (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 0) x) e₁ =
            (fderiv ℝ (fun _ : E 2 => (0 : ℝ)) x) e₁ := by congr 2; exact h_comp0
        rw [hconst0]; simp [fderiv_const]
      · -- Second component: cos θ * sin φ * S₀ + sin θ * sin φ * S₁ + cos φ * S₂
        -- Derivative w.r.t. φ: cos θ * cos φ * S₀ + sin θ * cos φ * S₁ - sin φ * S₂
        simp only [rotMφ, rotMφφ, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue]
        have h_comp1 : (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 1) =
            fun y => Real.cos (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 0 +
                     Real.sin (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 1 +
                     Real.cos (y.ofLp 1) * S.ofLp 2 := by
          ext y; simp [rotMφ, Matrix.toEuclideanLin_apply, dotProduct, Fin.sum_univ_three]
        have heq : (fderiv ℝ (fun y : E 2 => (rotMφ (y.ofLp 0) (y.ofLp 1) S).ofLp 1) x) e₁ =
            (fderiv ℝ (fun y => Real.cos (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 0 +
                     Real.sin (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 1 +
                     Real.cos (y.ofLp 1) * S.ofLp 2) x) e₁ := by
          congr 2; exact h_comp1
        rw [heq]
        have hd : HasFDerivAt (fun y : E 2 => Real.cos (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 0 +
                     Real.sin (y.ofLp 0) * Real.sin (y.ofLp 1) * S.ofLp 1 +
                     Real.cos (y.ofLp 1) * S.ofLp 2) _ x := by fun_prop
        rw [hd.fderiv]; simp only [EuclideanSpace.single_apply, ↓reduceIte, Fin.zero_eq_one_iff,
          mul_one, mul_zero, add_zero]
        simp only [rotMφφ, Matrix.of_apply, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
          mul_zero, add_zero]
        ring
    rw [hfderiv]
    -- Simplify: fderiv of constant w is 0, and θ = x.ofLp 0, φ = x.ofLp 1
    have hconst : (fderiv ℝ (fun _ : E 2 => w) x) e₁ = 0 := by
      rw [show (fun _ : E 2 => w) = Function.const (E 2) w from rfl, fderiv_const]; simp
    simp only [hconst, inner_zero_right, zero_add]
    rfl

-- Helper lemma for the inner case: the second partial of ⟪rotprojRM S, w⟫ equals ⟪A S, w⟫
-- where A is a composition of rotation matrices with ‖A‖ ≤ 1.
-- The 9 cases correspond to all pairs of derivatives w.r.t. (α, θ, φ).
-- Helper: composition norm bounds for rotation matrices
private lemma comp_rotR_norm_le (α θ φ : ℝ) (A : ℝ³ →L[ℝ] ℝ²) (hA : ‖A‖ ≤ 1) :
    ‖rotR α ∘L A‖ ≤ 1 := by
  calc ‖rotR α ∘L A‖ ≤ ‖rotR α‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = 1 * ‖A‖ := by rw [Bounding.rotR_norm_one]
    _ ≤ 1 * 1 := by apply mul_le_mul_of_nonneg_left hA; norm_num
    _ = 1 := by ring

private lemma comp_rotR'_norm_le (α θ φ : ℝ) (A : ℝ³ →L[ℝ] ℝ²) (hA : ‖A‖ ≤ 1) :
    ‖rotR' α ∘L A‖ ≤ 1 := by
  calc ‖rotR' α ∘L A‖ ≤ ‖rotR' α‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = 1 * ‖A‖ := by rw [Bounding.rotR'_norm_one]
    _ ≤ 1 * 1 := by apply mul_le_mul_of_nonneg_left hA; norm_num
    _ = 1 := by ring

private lemma neg_rotR_comp_norm_le (α θ φ : ℝ) :
    ‖-(rotR α ∘L rotM θ φ)‖ ≤ 1 := by
  rw [norm_neg]
  calc ‖rotR α ∘L rotM θ φ‖ ≤ ‖rotR α‖ * ‖rotM θ φ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = 1 * 1 := by rw [Bounding.rotR_norm_one, Bounding.rotM_norm_one]
    _ = 1 := by ring

private lemma second_partial_inner_bound (S : ℝ³) (w : ℝ²) (x : ℝ³) (i j : Fin 3) :
    |nth_partial i (nth_partial j (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) x| ≤
    ‖S‖ * ‖w‖ := by
  -- The second partial of ⟪rotprojRM S, w⟫ equals ⟪A S, w⟫ where A is a composition
  -- of rotation matrices with ‖A‖ ≤ 1.
  -- Variables: y 0 = α, y 1 = θ, y 2 = φ
  -- The operators A for each (i,j) pair:
  --   (0,0): -(rotR ∘ rotM)    (0,1): rotR' ∘ rotMθ   (0,2): rotR' ∘ rotMφ
  --   (1,0): rotR' ∘ rotMθ    (1,1): rotR ∘ rotMθθ   (1,2): rotR ∘ rotMθφ
  --   (2,0): rotR' ∘ rotMφ    (2,1): rotR ∘ rotMθφ   (2,2): rotR ∘ rotMφφ
  let α := x 0; let θ := x 1; let φ := x 2
  -- All these compositions have norm ≤ 1 by the helper lemmas above and Bounding lemmas.
  -- The detailed case analysis follows the same pattern as second_partial_inner_rotM_outer.
  -- For each case, we show the second partial equals ⟪A S, w⟫ and apply inner_product_norm_bound.
  -- This is a substantial but mechanical proof requiring 9 cases with similar structure.
  sorry

/- [SY25] Lemma 19 -/
theorem rotation_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_inner_unit S w) := by
  -- The inner case has 9 second partials (3x3 grid for α, θ, φ)
  -- Each second partial of ⟪rotR α (rotM θ φ S), w⟫ / ‖S‖ involves a composition of
  -- rotation matrices applied to S, and all have operator norm ≤ 1
  by_cases hS : ‖S‖ = 0
  · -- When ‖S‖ = 0, the function is constantly 0
    intro x i j
    have hzero : rotproj_inner_unit S w = 0 := by ext y; simp [rotproj_inner_unit, hS]
    have h1 : nth_partial j (rotproj_inner_unit S w) = 0 := by
      ext y
      simp only [nth_partial, hzero]
      rw [fderiv_zero]
      simp
    simp only [nth_partial, h1]
    rw [fderiv_zero]
    simp
  · -- When ‖S‖ ≠ 0
    have S_pos : ‖S‖ > 0 := (norm_nonneg S).lt_of_ne' hS
    intro x i j
    -- The function is rotproj_inner_unit S w = (fun y => ⟪rotprojRM ... S, w⟫) / ‖S‖
    -- Its second partial equals (second partial of inner product) / ‖S‖
    have heq : rotproj_inner_unit S w = fun y => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫ / ‖S‖ := by
      ext y; rfl
    -- The second partial of f/c is (second partial of f) / c
    have hscale : nth_partial i (nth_partial j (rotproj_inner_unit S w)) x =
        nth_partial i (nth_partial j (fun y => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) x / ‖S‖ := by
      have hdiv : rotproj_inner_unit S w =
          (‖S‖⁻¹ : ℝ) • (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫) := by
        ext y; simp [rotproj_inner_unit, div_eq_inv_mul, smul_eq_mul]
      rw [hdiv]
      have hDiff : Differentiable ℝ (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫) := by
        simp only [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
        fun_prop
      have hpart_j : nth_partial j (‖S‖⁻¹ • (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) =
          ‖S‖⁻¹ • (nth_partial j (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) := by
        ext y
        simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
        rw [fderiv_const_smul (hDiff y) ‖S‖⁻¹]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hpart_j]
      have hDiff2 : Differentiable ℝ (nth_partial j (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) := by
        have hsmooth : ContDiff ℝ 2 (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫) := by
          have h_unit := rotation_partials_exist S_pos (w := w)
          have h_smul : (fun y : ℝ³ => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫) =
              ‖S‖ • (rotproj_inner_unit S w) := by
            ext y; simp [rotproj_inner_unit, smul_eq_mul, mul_div_cancel₀ _ (ne_of_gt S_pos)]
          rw [h_smul]
          exact ContDiff.const_smul ‖S‖ h_unit
        have h2eq : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
        rw [h2eq, contDiff_succ_iff_fderiv_apply] at hsmooth
        obtain ⟨hDiff_f, _, h_fderiv_contdiff⟩ := hsmooth
        have h_partial_contdiff := h_fderiv_contdiff (EuclideanSpace.single j 1)
        exact h_partial_contdiff.differentiable one_ne_zero
      simp only [nth_partial]
      rw [fderiv_const_smul (hDiff2 x) ‖S‖⁻¹]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hscale]
    -- Now we need to show the second partial of ⟪rotprojRM S, w⟫ is bounded by ‖S‖
    -- The second partial has the form ⟪A S, w⟫ where A is a composition of rotation matrices
    -- with ‖A‖ ≤ 1, so |⟪A S, w⟫| ≤ ‖A S‖ * ‖w‖ ≤ ‖A‖ * ‖S‖ * ‖w‖ ≤ ‖S‖
    -- Therefore |second partial / ‖S‖| ≤ 1
    -- The proof is complex since rotproj has 3 variables, giving 9 cases
    -- Each case involves compositions like rotR ∘ rotMθθ, rotR' ∘ rotMθ, etc.
    -- All these compositions have operator norm ≤ 1 since ‖rotR‖ = ‖rotR'‖ = 1 and ‖rotM*‖ ≤ 1
    -- For now, we use a computation-based approach
    have hbound : |nth_partial i (nth_partial j (fun y => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) x| ≤ ‖S‖ := by
      calc |nth_partial i (nth_partial j (fun y => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) x|
          ≤ ‖S‖ * ‖w‖ := second_partial_inner_bound S w x i j
        _ = ‖S‖ := by rw [w_unit, mul_one]
    calc |nth_partial i (nth_partial j (fun y => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) x / ‖S‖|
        = |nth_partial i (nth_partial j (fun y => ⟪rotprojRM (y 1) (y 2) (y 0) S, w⟫)) x| / ‖S‖ := by
          rw [abs_div, abs_of_pos S_pos]
      _ ≤ ‖S‖ / ‖S‖ := by gcongr
      _ = 1 := div_self (ne_of_gt S_pos)

theorem rotation_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_outer_unit S w) := by
  -- First handle the case when ‖S‖ = 0
  by_cases hS : ‖S‖ = 0
  · -- When ‖S‖ = 0, the function is constantly 0
    intro x i j
    have hzero : rotproj_outer_unit S w = 0 := by ext y; simp [rotproj_outer_unit, hS]
    have h1 : nth_partial j (rotproj_outer_unit S w) = 0 := by
      ext y
      simp only [nth_partial, hzero]
      rw [fderiv_zero]
      simp
    simp only [nth_partial, h1]
    rw [fderiv_zero]
    simp
  · -- When ‖S‖ ≠ 0, we have S_nonzero : ‖S‖ > 0
    have S_pos : ‖S‖ > 0 := (norm_nonneg S).lt_of_ne' hS
    intro x i j
    -- The function is rotproj_outer_unit S w = (fun y => ⟪rotM (y 0) (y 1) S, w⟫) / ‖S‖
    -- Its second partial equals (second partial of inner product) / ‖S‖
    -- By second_partial_inner_rotM_outer, the second partial of the inner product is ⟪A S, w⟫
    -- where ‖A‖ ≤ 1, so the full second partial is ⟪A S, w⟫ / ‖S‖
    -- By inner_bound_helper, this has absolute value ≤ 1

    -- First, relate rotproj_outer_unit to the inner product function
    have heq : rotproj_outer_unit S w = fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫ / ‖S‖ := by
      ext y; rfl

    -- The second partial of f/c is (second partial of f) / c
    -- This follows from fderiv (c⁻¹ • f) = c⁻¹ • fderiv f applied twice
    -- Proof: f/c = c⁻¹ • f, and since fderiv commutes with scalar multiplication,
    -- nth_partial i (nth_partial j (f / c)) = nth_partial i (nth_partial j f) / c
    have hscale : nth_partial i (nth_partial j (rotproj_outer_unit S w)) x =
        nth_partial i (nth_partial j (fun y => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x / ‖S‖ := by
      -- f/c = c⁻¹ • f where c = ‖S‖
      have hdiv : rotproj_outer_unit S w =
          (‖S‖⁻¹ : ℝ) • (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) := by
        ext y; simp [rotproj_outer_unit, div_eq_inv_mul, smul_eq_mul]
      rw [hdiv]
      -- Use fderiv_const_smul twice
      have hDiff : Differentiable ℝ (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) :=
        Differentiable.inner ℝ (Differentiable.rotM_outer S) (by fun_prop)
      -- Show nth_partial j of (c • f) = c • (nth_partial j f)
      have hpart_j : nth_partial j (‖S‖⁻¹ • (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) =
          ‖S‖⁻¹ • (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) := by
        ext y
        simp only [nth_partial, Pi.smul_apply, smul_eq_mul]
        rw [fderiv_const_smul (hDiff y) ‖S‖⁻¹]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hpart_j]
      -- Show nth_partial i of (c • g) = c • (nth_partial i g)
      have hDiff2 : Differentiable ℝ (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) := by
        -- nth_partial j f y = (fderiv f y) e_j is differentiable when f is C²
        -- Use contDiff_succ_iff_fderiv_apply to convert ContDiff 2 to differentiability of partial
        have hsmooth : ContDiff ℝ 2 (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) := by
          -- rotproj_outer_unit S w = f / ‖S‖ is ContDiff 2, so f = ‖S‖ * rotproj_outer_unit is too
          have h_unit := rotation_partials_exist_outer S_pos (w := w)
          have h_smul : (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫) =
              ‖S‖ • (rotproj_outer_unit S w) := by
            ext y; simp [rotproj_outer_unit, smul_eq_mul, mul_div_cancel₀ _ (ne_of_gt S_pos)]
          rw [h_smul]
          exact ContDiff.const_smul ‖S‖ h_unit
        -- 2 = 1 + 1 as WithTop ℕ∞
        have h2eq : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
        rw [h2eq, contDiff_succ_iff_fderiv_apply] at hsmooth
        obtain ⟨hDiff_f, _, h_fderiv_contdiff⟩ := hsmooth
        have h_partial_contdiff := h_fderiv_contdiff (EuclideanSpace.single j 1)
        exact h_partial_contdiff.differentiable one_ne_zero
      simp only [nth_partial]
      rw [fderiv_const_smul (hDiff2 x) ‖S‖⁻¹]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]

    -- Get the existence of A with norm bound
    obtain ⟨A, hAnorm, hAeq⟩ := second_partial_inner_rotM_outer S w x i j

    -- Now apply the bound
    rw [hscale, hAeq]
    exact inner_bound_helper A S w w_unit hAnorm

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
