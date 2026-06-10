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
  grind [Real.sin_sq]

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

/--
Bessel's inequality in coordinates: if the rows `a = (a0, a1, a2)` and
`b = (b0, b1, b2)` are orthogonal and each have norm at most one, then
`(a ⬝ᵥ v)² + (b ⬝ᵥ v)² ≤ ‖v‖²`.

The certificate combines the Lagrange identity (Cauchy–Schwarz) for each row
with the Gram determinant identity
`|a|²|b|²|v|² = |b|²(a⬝v)² + |a|²(b⬝v)² + det[a;b;v]²`, which holds when `a ⬝ᵥ b = 0`.
-/
private lemma inner_sq_add_inner_sq_le {a0 a1 a2 b0 b1 b2 x y z : ℝ}
    (horth : a0 * b0 + a1 * b1 + a2 * b2 = 0)
    (h0 : a0^2 + a1^2 + a2^2 ≤ 1) (h1 : b0^2 + b1^2 + b2^2 ≤ 1) :
    (a0*x + a1*y + a2*z)^2 + (b0*x + b1*y + b2*z)^2 ≤ x^2 + y^2 + z^2 := by
  -- Cauchy–Schwarz for each row, via the Lagrange identity.
  have hP : 0 ≤ (a0^2+a1^2+a2^2) * (x^2+y^2+z^2) - (a0*x + a1*y + a2*z)^2 := by
    have h : (a0^2+a1^2+a2^2) * (x^2+y^2+z^2) - (a0*x + a1*y + a2*z)^2
        = (a0*y - a1*x)^2 + (a0*z - a2*x)^2 + (a1*z - a2*y)^2 := by ring
    rw [h]; positivity
  have hQ : 0 ≤ (b0^2+b1^2+b2^2) * (x^2+y^2+z^2) - (b0*x + b1*y + b2*z)^2 := by
    have h : (b0^2+b1^2+b2^2) * (x^2+y^2+z^2) - (b0*x + b1*y + b2*z)^2
        = (b0*y - b1*x)^2 + (b0*z - b2*x)^2 + (b1*z - b2*y)^2 := by ring
    rw [h]; positivity
  have e1 : 0 ≤ (1 - (b0^2+b1^2+b2^2)) *
      ((a0^2+a1^2+a2^2) * (x^2+y^2+z^2) - (a0*x + a1*y + a2*z)^2) :=
    mul_nonneg (by linarith) hP
  have e2 : 0 ≤ (1 - (a0^2+a1^2+a2^2)) *
      ((b0^2+b1^2+b2^2) * (x^2+y^2+z^2) - (b0*x + b1*y + b2*z)^2) :=
    mul_nonneg (by linarith) hQ
  have e3 : 0 ≤ (1 - (a0^2+a1^2+a2^2)) * ((1 - (b0^2+b1^2+b2^2)) * (x^2+y^2+z^2)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by positivity))
  -- The defect decomposes into the nonnegative pieces above plus the square of
  -- det[a;b;v]; orthogonality of the rows enters through the Gram identity.
  have key : x^2+y^2+z^2 - (a0*x + a1*y + a2*z)^2 - (b0*x + b1*y + b2*z)^2
      = (1 - (b0^2+b1^2+b2^2)) *
          ((a0^2+a1^2+a2^2) * (x^2+y^2+z^2) - (a0*x + a1*y + a2*z)^2)
      + (1 - (a0^2+a1^2+a2^2)) *
          ((b0^2+b1^2+b2^2) * (x^2+y^2+z^2) - (b0*x + b1*y + b2*z)^2)
      + (1 - (a0^2+a1^2+a2^2)) * ((1 - (b0^2+b1^2+b2^2)) * (x^2+y^2+z^2))
      + (a0*(b1*z - b2*y) - a1*(b0*z - b2*x) + a2*(b0*y - b1*x))^2 := by
    linear_combination ((a0*b0 + a1*b1 + a2*b2) * (x^2+y^2+z^2)
      - 2 * (a0*x + a1*y + a2*z) * (b0*x + b1*y + b2*z)) * horth
  linarith [e1, e2, e3, key,
    sq_nonneg (a0*(b1*z - b2*y) - a1*(b0*z - b2*x) + a2*(b0*y - b1*x))]

/--
A `2 × 3` matrix whose rows are orthogonal to each other and have norm at most
one has operator norm at most one (as a map `ℝ³ →L[ℝ] ℝ²` between Euclidean
spaces). This is Bessel's inequality.
-/
theorem opNorm_le_one_of_orthogonal_rows {A : Matrix (Fin 2) (Fin 3) ℝ}
    (horth : A 0 ⬝ᵥ A 1 = 0) (h0 : A 0 ⬝ᵥ A 0 ≤ 1) (h1 : A 1 ⬝ᵥ A 1 ≤ 1) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
  simp only [dotProduct, Fin.sum_univ_three, ← pow_two] at horth h0 h1
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two,
    Fin.sum_univ_three, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  exact inner_sq_add_inner_sq_le horth h0 h1

private lemma mul_sin_sq_add_cos_sq (k θ : ℝ) : k * (Real.sin θ ^ 2 + Real.cos θ ^ 2) = k := by
  rw [Real.sin_sq_add_cos_sq, mul_one]

theorem rotMθ_norm_le_one (θ φ : ℝ) : ‖rotMθ θ φ‖ ≤ 1 := by
  refine opNorm_le_one_of_orthogonal_rows ?_ ?_ ?_ <;>
    simp [rotMθ_mat, dotProduct, Fin.sum_univ_three]
  all_goals
    linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, mul_sin_sq_add_cos_sq (Real.sin φ ^ 2) θ,
      Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ,
      Real.cos_sq_le_one φ, Real.sin_sq_le_one φ]

theorem rotMφ_norm_le_one (θ φ : ℝ) : ‖rotMφ θ φ‖ ≤ 1 := by
  refine opNorm_le_one_of_orthogonal_rows ?_ ?_ ?_ <;>
    simp [rotMφ_mat, dotProduct, Fin.sum_univ_three]
  all_goals
    linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, mul_sin_sq_add_cos_sq (Real.sin φ ^ 2) θ,
      Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ,
      Real.cos_sq_le_one φ, Real.sin_sq_le_one φ]

-- Operator norm bounds for second derivative matrices
theorem rotMθθ_norm_le_one (θ φ : ℝ) : ‖rotMθθ θ φ‖ ≤ 1 := by
  refine opNorm_le_one_of_orthogonal_rows ?_ ?_ ?_ <;>
    simp [rotMθθ_mat, dotProduct, Fin.sum_univ_three]
  all_goals
    linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, mul_sin_sq_add_cos_sq (Real.sin φ ^ 2) θ,
      Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ,
      Real.cos_sq_le_one φ, Real.sin_sq_le_one φ]

theorem rotMθφ_norm_le_one (θ φ : ℝ) : ‖rotMθφ θ φ‖ ≤ 1 := by
  refine opNorm_le_one_of_orthogonal_rows ?_ ?_ ?_ <;>
    simp [rotMθφ_mat, dotProduct, Fin.sum_univ_three]
  all_goals
    linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, mul_sin_sq_add_cos_sq (Real.sin φ ^ 2) θ,
      Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ,
      Real.cos_sq_le_one φ, Real.sin_sq_le_one φ]

theorem rotMφφ_norm_le_one (θ φ : ℝ) : ‖rotMφφ θ φ‖ ≤ 1 := by
  refine opNorm_le_one_of_orthogonal_rows ?_ ?_ ?_ <;>
    simp [rotMφφ_mat, dotProduct, Fin.sum_univ_three]
  all_goals
    linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, mul_sin_sq_add_cos_sq (Real.sin φ ^ 2) θ,
      Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ,
      Real.cos_sq_le_one φ, Real.sin_sq_le_one φ]

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

lemma vecX_norm_one (θ φ : ℝ) : ‖vecX θ φ‖ = 1 := by
  simp only [vecX_identity, ContinuousLinearMap.coe_comp', Function.comp_apply,
    Rz_preserves_norm, Ry_preserves_norm]
  simp [PiLp.norm_eq_of_L2, Fin.sum_univ_three]

theorem rotM_norm_one (θ φ : ℝ) : ‖rotM θ φ‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_one_of_orthogonal_rows ?_ ?_ ?_ <;>
      simp [rotM_mat, dotProduct, Fin.sum_univ_three]
    all_goals
      linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, Real.sin_sq_add_cos_sq θ,
        Real.sin_sq_add_cos_sq φ]
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
