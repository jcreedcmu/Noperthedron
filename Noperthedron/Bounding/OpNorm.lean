import Noperthedron.Basic

namespace Bounding

open scoped Matrix
open scoped RealInnerProductSpace

theorem norm_one_of_preserves_norm {n m : ℕ} [NeZero n] {f : E n →L[ℝ] E m} (hf : (v : E n) → ‖f v‖ = ‖v‖) :
    ‖f‖ = 1 := by
  have decrease (x : E n) : ‖f x‖ ≤ 1 * ‖x‖ := by rw [hf x]; simp
  have increase (N : ℝ) (hN : N ≥ 0) (k : ∀ (x : E n), ‖f x‖ ≤ N * ‖x‖) : 1 ≤ N := by
    let e : E n := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have z := k e; rw [hf, he, mul_one] at z; exact z
  exact ContinuousLinearMap.opNorm_eq_of_bounds (by norm_num) decrease increase

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

The matrix is stated as a literal so that uses can instantiate it by unification,
leaving only scalar side goals.
-/
theorem opNorm_le_one_of_orthogonal_rows {a b c d e f : ℝ}
    (horth : a * d + b * e + c * f = 0)
    (h0 : a^2 + b^2 + c^2 ≤ 1) (h1 : d^2 + e^2 + f^2 ≤ 1) :
    ‖(!![a, b, c; d, e, f]).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two,
    Fin.sum_univ_three, LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.cons_mulVec, Matrix.cons_dotProduct,
    Matrix.dotProduct_of_isEmpty, Matrix.empty_mulVec, Fin.isValue, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  linarith [inner_sq_add_inner_sq_le (x := v.ofLp 0) (y := v.ofLp 1) (z := v.ofLp 2) horth h0 h1]

private lemma mul_sin_sq_add_cos_sq (k θ : ℝ) : k * (Real.sin θ ^ 2 + Real.cos θ ^ 2) = k := by
  rw [Real.sin_sq_add_cos_sq, mul_one]

theorem rotMθ_norm_le_one (θ φ : ℝ) : ‖rotMθ θ φ‖ ≤ 1 :=
  opNorm_le_one_of_orthogonal_rows
    (by ring)
    (by linarith [Real.sin_sq_add_cos_sq θ])
    (by linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, Real.cos_sq_le_one φ])

theorem rotMφ_norm_le_one (θ φ : ℝ) : ‖rotMφ θ φ‖ ≤ 1 :=
  opNorm_le_one_of_orthogonal_rows
    (by ring)
    (by linarith [zero_le_one (α := ℝ)])
    (by linarith [mul_sin_sq_add_cos_sq (Real.sin φ ^ 2) θ, Real.sin_sq_add_cos_sq φ])

-- Operator norm bounds for second derivative matrices
theorem rotMθθ_norm_le_one (θ φ : ℝ) : ‖rotMθθ θ φ‖ ≤ 1 :=
  opNorm_le_one_of_orthogonal_rows
    (by ring)
    (by linarith [Real.sin_sq_add_cos_sq θ])
    (by linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, Real.cos_sq_le_one φ])

theorem rotMθφ_norm_le_one (θ φ : ℝ) : ‖rotMθφ θ φ‖ ≤ 1 :=
  opNorm_le_one_of_orthogonal_rows
    (by ring)
    (by linarith [zero_le_one (α := ℝ)])
    (by linarith [mul_sin_sq_add_cos_sq (Real.sin φ ^ 2) θ, Real.sin_sq_le_one φ])

theorem rotMφφ_norm_le_one (θ φ : ℝ) : ‖rotMφφ θ φ‖ ≤ 1 :=
  opNorm_le_one_of_orthogonal_rows
    (by ring)
    (by linarith [zero_le_one (α := ℝ)])
    (by linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, Real.sin_sq_add_cos_sq φ])

/- Rotations as linear isometries -/

lemma rot3_mat_mem_O3 (d : Fin 3) (θ : ℝ) :
    rot3_mat d θ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  unfold rot3_mat
  fin_cases d <;>
  · constructor <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
      · try simp [Matrix.mul_apply, Fin.sum_univ_succ]
        try ring_nf
        try simp [Real.sin_sq]

noncomputable def OrthogonalGroup.toLinearEquiv {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ)
    : Euc(n) ≃ₗ[ℝ] Euc(n) :=
  WithLp.linearEquiv 2 ℝ (Fin n → ℝ) ≪≫ₗ
    Matrix.UnitaryGroup.toLinearEquiv A ≪≫ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm

lemma OrthogonalGroup.toLinearEquiv_apply {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Euc(n)) :
    OrthogonalGroup.toLinearEquiv A x = A.1.mulVec x := by
  rfl

/-- An orthogonal matrix gives a linear isometry equivalence of Euclidean space. -/
noncomputable def OrthogonalGroup.toLinearIsometryEquiv {n : ℕ}
    (A : Matrix.orthogonalGroup (Fin n) ℝ) : Euc(n) ≃ₗᵢ[ℝ] Euc(n) :=
  (OrthogonalGroup.toLinearEquiv A).isometryOfInner fun x y => by
    have hA : A.1ᵀ * A.1 = 1 := A.2.1
    have key : (A.1 *ᵥ x) ⬝ᵥ (A.1 *ᵥ y) = x ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hA, Matrix.vecMul_one]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      OrthogonalGroup.toLinearEquiv_apply]
    simpa [dotProduct, mul_comm] using key

lemma OrthogonalGroup.toLinearIsometryEquiv_apply {n : ℕ}
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Euc(n)) :
    OrthogonalGroup.toLinearIsometryEquiv A x = A.1.mulVec x :=
  OrthogonalGroup.toLinearEquiv_apply A x

/-- The rotation `rot3 d θ`, bundled as a linear isometry equivalence. -/
noncomputable def rot3Isometry (d : Fin 3) (θ : ℝ) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  OrthogonalGroup.toLinearIsometryEquiv ⟨rot3_mat d θ, rot3_mat_mem_O3 d θ⟩

lemma rot3_eq_rot3Isometry (d : Fin 3) (θ : ℝ) :
    (rot3 d θ : ℝ³ →L[ℝ] ℝ³) = (rot3Isometry d θ).toLinearIsometry.toContinuousLinearMap := by
  ext v
  fin_cases d <;> rfl

theorem rot3_preserves_norm (d : Fin 3) (α : ℝ) (v : ℝ³) : ‖rot3 d α v‖ = ‖v‖ := by
  rw [rot3_eq_rot3Isometry]
  exact (rot3Isometry d α).norm_map v

lemma rot3Isometry_apply (d : Fin 3) (θ : ℝ) (v : ℝ³) :
    rot3Isometry d θ v = rot3 d θ v := by
  rw [rot3_eq_rot3Isometry]
  rfl

lemma rot3_neg_apply (d : Fin 3) (θ : ℝ) (v : ℝ³) : rot3 d θ (rot3 d (-θ) v) = v := by
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← AddChar.map_add_eq_mul]
  simp

/-- Moving a rotation to the other side of an inner product inverts its angle. -/
lemma inner_rot3_left (d : Fin 3) (θ : ℝ) (a b : ℝ³) :
    ⟪rot3 d θ a, b⟫ = ⟪a, rot3 d (-θ) b⟫ := by
  nth_rw 1 [show b = rot3 d θ (rot3 d (-θ) b) from (rot3_neg_apply d θ b).symm]
  rw [← rot3Isometry_apply, ← rot3Isometry_apply]
  exact (rot3Isometry d θ).inner_map_map a (rot3 d (-θ) b)

/- [SY25] Lemma 9 -/

theorem lemma9 {d : Fin 3} (α : ℝ) : ‖rot3 d α‖ = 1 := by
  rw [rot3_eq_rot3Isometry]
  exact (rot3Isometry d α).toLinearIsometry.norm_toContinuousLinearMap

theorem rot3_preserves_op_norm (d : Fin 3) (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)) :
    ‖(rot3 d α : ℝ³ →L[ℝ] ℝ³) ∘L A‖ = ‖A‖ := by
  rw [rot3_eq_rot3Isometry]
  exact (rot3Isometry d α).toLinearIsometry.norm_toContinuousLinearMap_comp

theorem rot3_comp_right_preserves_op_norm (d : Fin 3) (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)) :
    ‖A ∘L (rot3 d α : ℝ³ →L[ℝ] ℝ³)‖ = ‖A‖ := by
  rw [rot3_eq_rot3Isometry]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv A (rot3Isometry d α)

theorem Rx_preserves_norm (α : ℝ) : ∀ (v : E 3), ‖(RxL α) v‖ = ‖v‖ :=
  rot3_preserves_norm 0 α

theorem Rx_norm_one (α : ℝ) : ‖RxL α‖ = 1 :=
  lemma9 (d := 0) α

theorem Rx_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RxL α).comp A‖ = ‖A‖ :=
  rot3_preserves_op_norm 0 α A

theorem Ry_preserves_norm (α : ℝ) : ∀ (v : E 3), ‖(RyL α) v‖ = ‖v‖ :=
  rot3_preserves_norm 1 α

theorem Ry_norm_one (α : ℝ) : ‖RyL α‖ = 1 :=
  lemma9 (d := 1) α

theorem Ry_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RyL α).comp A‖ = ‖A‖ :=
  rot3_preserves_op_norm 1 α A

theorem Ry_comp_right_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖A ∘L (RyL α)‖ = ‖A‖ :=
  rot3_comp_right_preserves_op_norm 1 α A

theorem Rz_preserves_norm (α : ℝ) : ∀ (v : E 3), ‖(RzL α) v‖ = ‖v‖ :=
  rot3_preserves_norm 2 α

theorem Rz_norm_one (α : ℝ) : ‖RzL α‖ = 1 :=
  lemma9 (d := 2) α

theorem Rz_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖(RzL α).comp A‖ = ‖A‖ :=
  rot3_preserves_op_norm 2 α A

theorem Rz_comp_right_preserves_op_norm (α : ℝ) (A : Euc(3) →L[ℝ] Euc(3)):
    ‖A ∘L (RzL α)‖ = ‖A‖ :=
  rot3_comp_right_preserves_op_norm 2 α A

lemma vecX_norm_one (θ φ : ℝ) : ‖vecX θ φ‖ = 1 := by
  simp only [vecX_identity, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Rz_preserves_norm, Ry_preserves_norm]
  simp [PiLp.norm_eq_of_L2, Fin.sum_univ_three]

theorem rotM_norm_one (θ φ : ℝ) : ‖rotM θ φ‖ = 1 := by
  refine le_antisymm ?_ ?_
  · exact opNorm_le_one_of_orthogonal_rows
      (by ring)
      (by linarith [Real.sin_sq_add_cos_sq θ])
      (by linarith [mul_sin_sq_add_cos_sq (Real.cos φ ^ 2) θ, Real.sin_sq_add_cos_sq φ])
  · rw [ContinuousLinearMap.norm_def]
    refine le_csInf ?_ ?_
    · exact ⟨‖rotM θ φ‖, norm_nonneg _, fun x => ContinuousLinearMap.le_opNorm _ _⟩
    · rintro b ⟨-, hb⟩
      specialize hb !₂[-Real.sin θ, Real.cos θ, 0]
      have h : Real.sin θ * (Real.cos θ * Real.cos φ) + -(Real.cos θ * (Real.sin θ * Real.cos φ)) = 0 := by
        ring
      simpa [rotM, rotM_mat, EuclideanSpace.norm_eq, Fin.sum_univ_succ, ←sq, h] using hb

theorem reduceL_norm : ‖reduceL‖ = 1 := by
  simpa [rotM, reduceL, rotM_mat] using Bounding.rotM_norm_one 0 0

end Bounding
