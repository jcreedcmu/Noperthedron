import Noperthedron.Basic

namespace Bounding

theorem norm_one_of_preserves_norm {n m : ℕ} [NeZero n] {f : E n →L[ℝ] E m} (hf : (v : E n) → ‖f v‖ = ‖v‖) :
    ‖f‖ = 1 := by
  have decrease (x : E n) : ‖f x‖ ≤ 1 * ‖x‖ := by rw [hf x]; simp
  have increase (N : ℝ) (hN : N ≥ 0) (k : ∀ (x : E n), ‖f x‖ ≤ N * ‖x‖) : 1 ≤ N := by
    let e : E n := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have z := k e; rw [hf, he, mul_one] at z; exact z
  exact ContinuousLinearMap.opNorm_eq_of_bounds (by norm_num) decrease increase

theorem norm_one_of_preserves_sq_norm {n m : ℕ} [NeZero n] {f : E n →L[ℝ] E m}
    (hf : (v : E n) → ‖f v‖^2 = ‖v‖^2) : ‖f‖ = 1 := by
  refine norm_one_of_preserves_norm ?_
  intro v
  suffices h : ‖f v‖^2 = ‖v‖^2 by simp_all
  exact hf v

theorem rotR_preserves_norm (α : ℝ) :
    ∀ (v : E 2), ‖rotR α v‖ = ‖v‖ := by
  intro v
  suffices h : ‖rotR α v‖^2 = ‖v‖^2 by simp_all
  simp only [rotR, rotR_mat, PiLp.norm_sq_eq_of_L2]
  simp only [AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.vec2_dotProduct, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, neg_mul]
  ring_nf
  convert_to (v 0)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2) + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2) = _
  · ring_nf
  simp

theorem rotR_norm_one (α : ℝ) : ‖rotR α‖ = 1 :=
  norm_one_of_preserves_norm (rotR_preserves_norm α)

theorem rotR'_preserves_norm (α : ℝ) :
    ∀ (v : E 2), ‖rotR' α v‖ = ‖v‖ := by
  intro v
  have heq : rotR' α v = rotR (α + Real.pi/2) v := by
    simp only [rotR', rotR'_mat, rotR, rotR_mat]
    simp only [LinearMap.coe_toContinuousLinearMap']
    ext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  rw [heq]
  exact rotR_preserves_norm (α + Real.pi/2) v

theorem rotR'_norm_one (α : ℝ) : ‖rotR' α‖ = 1 :=
  norm_one_of_preserves_norm (rotR'_preserves_norm α)

theorem rotMθ_norm_le_one (θ φ : ℝ) : ‖rotMθ θ φ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  have h_expand :
      (-Real.cos θ * v 0 - Real.sin θ * v 1) ^ 2 +
       (Real.sin θ * Real.cos φ * v 0 - Real.cos θ * Real.cos φ * v 1) ^ 2 ≤
      v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    -- Row 0 has norm 1 (cos² + sin² = 1), row 1 has norm |cos φ| ≤ 1
    nlinarith [sq_nonneg (Real.sin θ * v 0 - Real.cos θ * v 1), sq_nonneg (v 2),
      Real.sin_sq_add_cos_sq θ, Real.cos_sq_le_one φ]
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.isValue,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, one_mul]
  convert Real.sqrt_le_sqrt h_expand using 1
  · simp only [rotMθ, rotMθ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
      Matrix.dotProduct_of_isEmpty, Matrix.empty_mulVec, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_mul, add_zero,
      zero_mul]
    ring_nf!
  · ring_nf

theorem rotMφ_norm_le_one (θ φ : ℝ) : ‖rotMφ θ φ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  have h_expand :
      0 ^ 2 +
       (Real.cos θ * Real.sin φ * v 0 + Real.sin θ * Real.sin φ * v 1 + Real.cos φ * v 2) ^ 2 ≤
      v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    -- Row 1 of rotMφ is [cos θ sin φ, sin θ sin φ, cos φ], a unit vector
    -- Cauchy-Schwarz via orthogonal decomposition
    set c := Real.cos θ; set s := Real.sin θ
    set cφ := Real.cos φ; set sφ := Real.sin φ
    set u := c * v 0 + s * v 1
    set w := s * v 0 - c * v 1
    have h₁ : c^2 + s^2 = 1 := by simp only [c, s]; linarith [Real.sin_sq_add_cos_sq θ]
    have h₂ : sφ^2 + cφ^2 = 1 := Real.sin_sq_add_cos_sq φ
    have huw : v 0 ^ 2 + v 1 ^ 2 = u^2 + w^2 :=
      by nlinarith [sq_nonneg c, sq_nonneg s, sq_nonneg (v 0), sq_nonneg (v 1)]
    have heq : c * sφ * v 0 + s * sφ * v 1 + cφ * v 2 = sφ * u + cφ * v 2 := by ring
    have hrot : u^2 + v 2 ^2 = (sφ * u + cφ * v 2)^2 + (cφ * u - sφ * v 2)^2 :=
      by nlinarith [sq_nonneg cφ, sq_nonneg sφ, sq_nonneg u, sq_nonneg (v 2)]
    have hw : 0 ≤ w^2 := sq_nonneg w
    have hcomp : 0 ≤ (cφ * u - sφ * v 2)^2 := sq_nonneg _
    simp only [heq, pow_two] at *
    linarith
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.isValue,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, one_mul]
  convert Real.sqrt_le_sqrt h_expand using 1
  · simp only [rotMφ, rotMφ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
      Matrix.dotProduct_of_isEmpty, Matrix.empty_mulVec, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, zero_mul]
    ring_nf!
  · ring_nf

-- Operator norm bounds for second derivative matrices
theorem rotMθθ_norm_le_one (θ φ : ℝ) : ‖rotMθθ θ φ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  have h_expand :
      (Real.sin θ * v 0 - Real.cos θ * v 1) ^ 2 +
       (Real.cos θ * Real.cos φ * v 0 + Real.sin θ * Real.cos φ * v 1) ^ 2 ≤
      v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    -- Row 0: [sin θ, -cos θ, 0], norm = 1
    -- Row 1: [cos θ * cos φ, sin θ * cos φ, 0], norm = |cos φ| ≤ 1
    nlinarith [sq_nonneg (Real.cos θ * v 0 + Real.sin θ * v 1), sq_nonneg (v 2),
      Real.sin_sq_add_cos_sq θ, Real.cos_sq_le_one φ]
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.isValue,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, one_mul]
  convert Real.sqrt_le_sqrt h_expand using 1
  · simp only [rotMθθ, rotMθθ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
      Matrix.dotProduct_of_isEmpty, Matrix.empty_mulVec, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, zero_mul]
    ring_nf!
  · ring_nf

theorem rotMθφ_norm_le_one (θ φ : ℝ) : ‖rotMθφ θ φ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  have h_expand :
      0 ^ 2 +
       (-Real.sin θ * Real.sin φ * v 0 + Real.cos θ * Real.sin φ * v 1) ^ 2 ≤
      v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    -- Row 0: [0, 0, 0], norm = 0
    -- Row 1: [-sin θ * sin φ, cos θ * sin φ, 0], norm = |sin φ| ≤ 1
    -- The key is: (-sin θ * v 0 + cos θ * v 1)² ≤ v 0² + v 1² (sin² + cos² = 1)
    -- Then multiply by sin² φ ≤ 1
    set c := Real.cos θ; set s := Real.sin θ
    set sφ := Real.sin φ
    set u := -s * v 0 + c * v 1  -- the term being multiplied by sin φ
    have hsc : s^2 + c^2 = 1 := Real.sin_sq_add_cos_sq θ
    have hu_bound : u^2 ≤ v 0^2 + v 1^2 := by
      have h := sq_nonneg (c * v 0 + s * v 1)
      nlinarith
    have hsφ : sφ^2 ≤ 1 := Real.sin_sq_le_one φ
    have h_main : (sφ * u)^2 ≤ v 0^2 + v 1^2 := by
      have hsφ_nn : 0 ≤ sφ^2 := sq_nonneg _
      calc (sφ * u)^2 = sφ^2 * u^2 := by ring
        _ ≤ 1 * u^2 := by apply mul_le_mul_of_nonneg_right hsφ (sq_nonneg _)
        _ = u^2 := by ring
        _ ≤ v 0^2 + v 1^2 := hu_bound
    have hv2 : 0 ≤ v 2^2 := sq_nonneg _
    have heq : -s * sφ * v 0 + c * sφ * v 1 = sφ * u := by ring
    simp only [heq, pow_two] at *
    linarith
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.isValue,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, one_mul]
  convert Real.sqrt_le_sqrt h_expand using 1
  · simp only [rotMθφ, rotMθφ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
      Matrix.dotProduct_of_isEmpty, Matrix.empty_mulVec, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_mul, add_zero,
      zero_mul]
    ring_nf!
  · ring_nf

theorem rotMφφ_norm_le_one (θ φ : ℝ) : ‖rotMφφ θ φ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  have h_expand :
      0 ^ 2 +
       (Real.cos θ * Real.cos φ * v 0 + Real.sin θ * Real.cos φ * v 1 - Real.sin φ * v 2) ^ 2 ≤
      v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    -- Row 0: [0, 0, 0], norm = 0
    -- Row 1: [cos θ * cos φ, sin θ * cos φ, -sin φ], this is a unit vector
    set c := Real.cos θ; set s := Real.sin θ
    set cφ := Real.cos φ; set sφ := Real.sin φ
    set u := c * v 0 + s * v 1
    set w := s * v 0 - c * v 1
    have h₁ : c^2 + s^2 = 1 := by simp only [c, s]; linarith [Real.sin_sq_add_cos_sq θ]
    have h₂ : cφ^2 + sφ^2 = 1 := Real.cos_sq_add_sin_sq φ
    have huw : v 0 ^ 2 + v 1 ^ 2 = u^2 + w^2 :=
      by nlinarith [sq_nonneg c, sq_nonneg s, sq_nonneg (v 0), sq_nonneg (v 1)]
    have heq : c * cφ * v 0 + s * cφ * v 1 - sφ * v 2 = cφ * u - sφ * v 2 := by ring
    have hrot : u^2 + v 2 ^2 = (cφ * u - sφ * v 2)^2 + (sφ * u + cφ * v 2)^2 :=
      by nlinarith [sq_nonneg cφ, sq_nonneg sφ, sq_nonneg u, sq_nonneg (v 2)]
    have hw : 0 ≤ w^2 := sq_nonneg w
    have hcomp : 0 ≤ (sφ * u + cφ * v 2)^2 := sq_nonneg _
    simp only [heq, pow_two] at *
    linarith
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.isValue,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, one_mul]
  convert Real.sqrt_le_sqrt h_expand using 1
  · simp only [rotMφφ, rotMφφ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
      Matrix.dotProduct_of_isEmpty, Matrix.empty_mulVec, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, zero_mul]
    ring_nf!
  · ring_nf

theorem Rx_preserves_norm (α : ℝ) :
    ∀ (v : E 3), ‖(RxL α) v‖ = ‖v‖ := by
  intro v
  suffices h : ‖(RxL α) v‖^2 = ‖v‖^2  by simp_all
  simp only [RxL, Rx_mat, PiLp.norm_sq_eq_of_L2]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec3_dotProduct,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Matrix.cons_val]
  ring_nf
  convert_to (v 0)^2
           + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 2)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           = _
  · ring_nf
  simp

/- [SY25] Lemma 9 -/

theorem Rx_norm_one (α : ℝ) : ‖RxL α‖ = 1 :=
  norm_one_of_preserves_norm (Rx_preserves_norm α)

theorem Rx_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RxL α).comp A‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply, Rx_preserves_norm]

theorem Ry_preserves_norm (α : ℝ) :
    ∀ (v : E 3), ‖(RyL α) v‖ = ‖v‖ := by
  intro v
  suffices h : ‖(RyL α) v‖^2 = ‖v‖^2  by simp_all
  simp only [RyL, Ry_mat, PiLp.norm_sq_eq_of_L2]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec3_dotProduct,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Matrix.cons_val]
  ring_nf
  convert_to (v 0)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
             + (v 1)^2
             + (v 2)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           = _
  · ring_nf
  simp only [Fin.isValue, Real.cos_sq_add_sin_sq, mul_one]

theorem Ry_norm_one (α : ℝ) : ‖RyL α‖ = 1 :=
  norm_one_of_preserves_norm (Ry_preserves_norm α)

theorem Ry_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RyL α).comp A‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply, Ry_preserves_norm]

theorem Ry_comp_right_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖A ∘L (RyL α)‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply]
  have h_sets_eq : {c : ℝ | 0 ≤ c ∧ ∀ x : Euc(3), ‖A (RyL α x)‖ ≤ c * ‖x‖} =
                   {c : ℝ | 0 ≤ c ∧ ∀ x : Euc(3), ‖A x‖ ≤ c * ‖x‖} := by
    have h_inv : ∀ x : Euc(3), ∃ y : Euc(3), RyL α y = x := by
      have h_inv : Function.Bijective (RyL α) := by
        have h_bijective : Function.Injective (RyL α) := by
          intro x y hxy
          have := Ry_preserves_norm α (x - y)
          simp only [map_sub, sub_self, norm_zero, hxy] at this
          exact sub_eq_zero.mp (norm_eq_zero.mp this.symm)
        exact ⟨h_bijective, LinearMap.surjective_of_injective h_bijective⟩
      exact h_inv.surjective
    ext c
    apply Iff.intro
    · intro hc;
      refine ⟨hc.1, fun x ↦ ?_⟩
      obtain ⟨ y, rfl ⟩ := h_inv x
      have := hc.2 y
      nth_rw 2 [←Ry_preserves_norm α] at this
      exact this
    · intro hc
      refine ⟨hc.1, fun x ↦ ?_⟩
      simpa only [Ry_preserves_norm α] using hc.2 (RyL α x)
  rw [h_sets_eq]

theorem Rz_preserves_norm (α : ℝ) :
    ∀ (v : E 3), ‖(RzL α) v‖ = ‖v‖ := by
  intro v
  suffices h : ‖(RzL α) v‖^2 = ‖v‖^2  by simp_all
  simp only [RzL, Rz_mat, PiLp.norm_sq_eq_of_L2]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, Matrix.vec3_dotProduct,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Matrix.cons_val]
  ring_nf
  convert_to (v 0)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 1)^2 * (Real.cos α ^ 2 + Real.sin α ^ 2)
           + (v 2)^2
           = _
  · ring_nf
  simp only [Fin.isValue, Real.cos_sq_add_sin_sq, mul_one]

theorem Rz_norm_one (α : ℝ) : ‖RzL α‖ = 1 :=
  norm_one_of_preserves_norm (Rz_preserves_norm α)

theorem Rz_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RzL α).comp A‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply, Rz_preserves_norm]

theorem Rz_comp_right_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖A ∘L (RzL α)‖ = ‖A‖ := by
  simp only [ContinuousLinearMap.norm_def]
  simp_rw [ContinuousLinearMap.comp_apply]
  have h_sets_eq : {c : ℝ | 0 ≤ c ∧ ∀ x : Euc(3), ‖A (RzL α x)‖ ≤ c * ‖x‖} =
                   {c : ℝ | 0 ≤ c ∧ ∀ x : Euc(3), ‖A x‖ ≤ c * ‖x‖} := by
    have h_inv : ∀ x : Euc(3), ∃ y : Euc(3), RzL α y = x := by
      have h_inv : Function.Bijective (RzL α) := by
        have h_bijective : Function.Injective (RzL α) := by
          intro x y hxy
          have := Rz_preserves_norm α (x - y)
          simp only [map_sub, sub_self, norm_zero, hxy] at this
          exact sub_eq_zero.mp (norm_eq_zero.mp this.symm)
        exact ⟨h_bijective, LinearMap.surjective_of_injective h_bijective⟩
      exact h_inv.surjective
    ext c
    apply Iff.intro
    · intro hc;
      refine ⟨hc.1, fun x ↦ ?_⟩
      obtain ⟨ y, rfl ⟩ := h_inv x
      have := hc.2 y
      nth_rw 2 [←Rz_preserves_norm α] at this
      exact this
    · intro hc
      refine ⟨hc.1, fun x ↦ ?_⟩
      simpa only [Rz_preserves_norm α] using hc.2 (RzL α x)
  rw [h_sets_eq]

theorem rotM_norm_one (θ φ : ℝ) : ‖rotM θ φ‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    have h_expand :
        (-Real.sin θ * v 0 + Real.cos θ * v 1) ^ 2 +
         (-Real.cos θ * Real.cos φ * v 0 - Real.sin θ * Real.cos φ * v 1 + Real.sin φ * v 2) ^ 2 ≤
        v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
      nlinarith [sq_nonneg (Real.sin θ * v 1 + Real.cos θ * v 0),
        sq_nonneg (Real.sin φ * (Real.cos θ * v 0 + Real.sin θ * v 1) + Real.cos φ * v 2),
        Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]
    simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.isValue,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, one_mul]
    convert Real.sqrt_le_sqrt h_expand using 1
    · simp only [rotM, rotM_mat, neg_mul, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
        Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
        zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, Matrix.empty_mulVec,
        Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring_nf!
    · ring_nf
  · rw [ContinuousLinearMap.norm_def]
    refine le_csInf ?_ ?_
    · exact ⟨‖rotM θ φ‖, norm_nonneg _, fun x => ContinuousLinearMap.le_opNorm _ _⟩
    · rintro b ⟨-, hb⟩
      specialize hb !₂[-Real.sin θ, Real.cos θ, 0]
      have h : Real.sin θ * (Real.cos θ * Real.cos φ) + -(Real.cos θ * (Real.sin θ * Real.cos φ)) = 0 := by
        ring
      simpa [rotM, rotM_mat, EuclideanSpace.norm_eq, Fin.sum_univ_succ, ←sq, h] using hb

theorem lemma9 {d : Fin 3} (α : ℝ) : ‖rot3 d α‖ = 1 := by
  fin_cases d
  all_goals simp only [rot3]
  · exact Rx_norm_one α
  · exact Ry_norm_one α
  · exact Rz_norm_one α

theorem reduceL_norm : ‖reduceL‖ = 1 := by
  simpa [rotM, reduceL, rotM_mat] using Bounding.rotM_norm_one 0 0

end Bounding
