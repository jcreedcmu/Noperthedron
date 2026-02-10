import Noperthedron.Bounding.OpNorm
import Noperthedron.RationalApprox.ApproximableMatrices

namespace RationalApprox

/-- Material for [SY25] Corollary 41 -/
def rotR_approx : Matrix (Fin 2) (Fin 2) DistLeKappaEntry :=
  !![(.one, .cos), (.one, .msin); (.one, .sin), (.one, .cos)]

def rotR'_approx : Matrix (Fin 2) (Fin 2) DistLeKappaEntry :=
  !![(.one, .msin), (.one, .mcos); (.one, .cos), (.one, .msin)]

def rotM_approx : Matrix (Fin 2) (Fin 3) DistLeKappaEntry :=
  !![(.msin, .one), (.cos, .one), (.zero, .zero);
     (.mcos, .cos), (.msin, .cos), (.one, .sin)]

def rotMθ_approx : Matrix (Fin 2) (Fin 3) DistLeKappaEntry :=
  !![(.mcos, .one), (.msin, .one), (.zero, .zero);
     (.sin, .cos), (.mcos, .cos), (.zero, .sin)]

def rotMφ_approx : Matrix (Fin 2) (Fin 3) DistLeKappaEntry :=
  !![(.msin, .zero), (.cos, .zero), (.zero, .zero);
     (.mcos, .msin), (.msin, .msin), (.one, .cos)]

def vecX_approx : Matrix (Fin 3) (Fin 1) DistLeKappaEntry :=
  !![ (.cos, .sin); (.sin, .sin); (.one, .cos) ]

/-- Proof of [SY25] Corollary 41 -/
theorem R_difference_norm_bounded (α : ℝ) (hα : α ∈ Set.Icc (-4) 4) : ‖rotR α - rotRℚ α‖ ≤ κ := by
  let z_ : Set.Icc (-4 : ℝ) 4 := ⟨0, by norm_num⟩
  let α_ : Set.Icc (-4 : ℝ) 4 := ⟨α, hα⟩

  have h : rotR α = clinActual rotR_approx z_ α_ := by
    simp only [rotR, rotR_mat, AddChar.coe_mk, clinActual, rotR_approx,
       EmbeddingLike.apply_eq_iff_eq, α_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  have h : rotRℚ α = clinApprox rotR_approx z_ α_ := by
    simp [rotRℚ, rotRℚ_mat, clinApprox, rotR_approx, α_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  exact norm_matrix_actual_approx_le_kappa (m := ⟨2, by norm_num⟩) (n := ⟨2, by norm_num⟩)
    rotR_approx z_ α_

theorem R'_difference_norm_bounded (α : ℝ) (hα : α ∈ Set.Icc (-4) 4) : ‖rotR' α - rotR'ℚ α‖ ≤ κ := by
  let z_ : Set.Icc (-4 : ℝ) 4 := ⟨0, by norm_num⟩
  let α_ : Set.Icc (-4 : ℝ) 4 := ⟨α, hα⟩

  have h : rotR' α = clinActual rotR'_approx z_ α_ := by
    simp only [rotR', rotR'_mat, clinActual, rotR'_approx,
       EmbeddingLike.apply_eq_iff_eq, α_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  have h : rotR'ℚ α = clinApprox rotR'_approx z_ α_ := by
    simp [rotR'ℚ, rotR'ℚ_mat, clinApprox, rotR'_approx, α_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  exact norm_matrix_actual_approx_le_kappa (m := ⟨2, by norm_num⟩) (n := ⟨2, by norm_num⟩)
    rotR'_approx z_ α_

theorem M_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖rotM θ φ - rotMℚ θ φ‖ ≤ κ := by
  let θ_ : Set.Icc (-4 : ℝ) 4 := ⟨θ, hθ⟩
  let φ_ : Set.Icc (-4 : ℝ) 4 := ⟨φ, hφ⟩

  have h : rotM θ φ = clinActual rotM_approx θ_ φ_ := by
    simp only [rotM, rotM_mat, clinActual, rotM_approx,
       EmbeddingLike.apply_eq_iff_eq, θ_, φ_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  have h : rotMℚ θ φ = clinApprox rotM_approx θ_ φ_ := by
    simp [rotMℚ, rotMℚ_mat, clinApprox, rotM_approx, θ_, φ_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  exact norm_matrix_actual_approx_le_kappa (m := ⟨2, by norm_num⟩) (n := ⟨3, by norm_num⟩)
    rotM_approx θ_ φ_

theorem Mθ_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖rotMθ θ φ - rotMθℚ θ φ‖ ≤ κ := by
  let θ_ : Set.Icc (-4 : ℝ) 4 := ⟨θ, hθ⟩
  let φ_ : Set.Icc (-4 : ℝ) 4 := ⟨φ, hφ⟩

  have h : rotMθ θ φ = clinActual rotMθ_approx θ_ φ_ := by
    simp only [rotMθ, rotMθ_mat, clinActual, rotMθ_approx,
       EmbeddingLike.apply_eq_iff_eq, θ_, φ_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  have h : rotMθℚ θ φ = clinApprox rotMθ_approx θ_ φ_ := by
    simp [rotMθℚ, rotMθℚ_mat, clinApprox, rotMθ_approx, θ_, φ_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  exact norm_matrix_actual_approx_le_kappa (m := ⟨2, by norm_num⟩) (n := ⟨3, by norm_num⟩)
    rotMθ_approx θ_ φ_

theorem Mφ_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖rotMφ θ φ - rotMφℚ θ φ‖ ≤ κ := by
  let θ_ : Set.Icc (-4 : ℝ) 4 := ⟨θ, hθ⟩
  let φ_ : Set.Icc (-4 : ℝ) 4 := ⟨φ, hφ⟩

  have h : rotMφ θ φ = clinActual rotMφ_approx θ_ φ_ := by
    simp only [rotMφ, rotMφ_mat, clinActual, rotMφ_approx,
       EmbeddingLike.apply_eq_iff_eq, θ_, φ_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  have h : rotMφℚ θ φ = clinApprox rotMφ_approx θ_ φ_ := by
    simp [rotMφℚ, rotMφℚ_mat, clinApprox, rotMφ_approx, θ_, φ_]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  exact norm_matrix_actual_approx_le_kappa (m := ⟨2, by norm_num⟩) (n := ⟨3, by norm_num⟩)
    rotMφ_approx θ_ φ_

theorem X_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖vecXL θ φ - vecXLℚ θ φ‖ ≤ κ := by
  let θ_ : Set.Icc (-4 : ℝ) 4 := ⟨θ, hθ⟩
  let φ_ : Set.Icc (-4 : ℝ) 4 := ⟨φ, hφ⟩

  have h : vecXL θ φ = clinActual vecX_approx θ_ φ_ := by
    simp only [vecXL, vecX_mat, clinActual, vecX_approx,  θ_, φ_,
        EmbeddingLike.apply_eq_iff_eq,]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  have h : vecXLℚ θ φ = clinApprox vecX_approx θ_ φ_ := by
    simp only [vecXLℚ, vecXℚ_mat, clinApprox, vecX_approx, θ_, φ_,
        EmbeddingLike.apply_eq_iff_eq,]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]

  exact norm_matrix_actual_approx_le_kappa (m := ⟨3, by norm_num⟩) (n := ⟨1, by norm_num⟩)
    vecX_approx θ_ φ_

theorem Rℚ_norm_bounded (α : ℝ) (hα : α ∈ Set.Icc (-4) 4) : ‖rotRℚ α‖ ≤ 1 + κ := by
  calc ‖rotRℚ α‖
  _ ≤ ‖rotR α‖ + ‖rotR α - rotRℚ α‖ := norm_le_insert (rotR α) (rotRℚ α)
  _ = 1        + ‖rotR α - rotRℚ α‖ := by rw [Bounding.rotR_norm_one]
  _ ≤ 1 + κ := by grw [R_difference_norm_bounded α hα]

theorem Mℚ_norm_bounded {θ φ : ℝ} (hθ : θ ∈ Set.Icc (-4) 4) (hφ : φ ∈ Set.Icc (-4) 4) : ‖rotMℚ θ φ‖ ≤ 1 + κ := by
  calc ‖rotMℚ θ φ‖
  _ ≤ ‖rotM θ φ‖ + ‖rotM θ φ - rotMℚ θ φ‖ := norm_le_insert (rotM θ φ) (rotMℚ θ φ)
  _ = 1        + ‖rotM θ φ - rotMℚ θ φ‖ := by rw [Bounding.rotM_norm_one]
  _ ≤ 1 + κ := by grw [M_difference_norm_bounded θ φ hθ hφ]

theorem R'ℚ_norm_bounded (α : ℝ) (hα : α ∈ Set.Icc (-4) 4) : ‖rotR'ℚ α‖ ≤ 1 + κ := by
  calc ‖rotR'ℚ α‖
  _ ≤ ‖rotR' α‖ + ‖rotR' α - rotR'ℚ α‖ := norm_le_insert (rotR' α) (rotR'ℚ α)
  _ = 1 + ‖rotR' α - rotR'ℚ α‖ := by rw [Bounding.rotR'_norm_one]
  _ ≤ 1 + κ := by grw [R'_difference_norm_bounded α hα]

theorem Mθℚ_norm_bounded {θ φ : ℝ} (hθ : θ ∈ Set.Icc (-4) 4) (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖rotMθℚ θ φ‖ ≤ 1 + κ := by
  calc ‖rotMθℚ θ φ‖
  _ ≤ ‖rotMθ θ φ‖ + ‖rotMθ θ φ - rotMθℚ θ φ‖ := norm_le_insert _ _
  _ ≤ 1 + ‖rotMθ θ φ - rotMθℚ θ φ‖ := by gcongr; exact Bounding.rotMθ_norm_le_one _ _
  _ ≤ 1 + κ := by gcongr; exact Mθ_difference_norm_bounded _ _ hθ hφ

theorem Mφℚ_norm_bounded {θ φ : ℝ} (hθ : θ ∈ Set.Icc (-4) 4) (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖rotMφℚ θ φ‖ ≤ 1 + κ := by
  calc ‖rotMφℚ θ φ‖
  _ ≤ ‖rotMφ θ φ‖ + ‖rotMφ θ φ - rotMφℚ θ φ‖ := norm_le_insert _ _
  _ ≤ 1 + ‖rotMφ θ φ - rotMφℚ θ φ‖ := by gcongr; exact Bounding.rotMφ_norm_le_one _ _
  _ ≤ 1 + κ := by gcongr; exact Mφ_difference_norm_bounded _ _ hθ hφ

/-- Convert `Set.Icc` membership from `ℤ` bounds to `ℝ` bounds. -/
lemma icc_int_to_real (x : Set.Icc ((-4 : ℤ)) 4) :
    (x : ℝ) ∈ Set.Icc ((-4 : ℝ)) 4 :=
  ⟨by exact_mod_cast x.property.1, by exact_mod_cast x.property.2⟩

/-- Common bound: ‖A P - Aℚ P_‖ ≤ 2κ + κ² when ‖A - Aℚ‖ ≤ κ, ‖Aℚ‖ ≤ 1 + κ,
‖P‖ ≤ 1, and ‖P - P_‖ ≤ κ. -/
lemma clm_approx_apply_sub {E F : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A Aℚ : E →L[ℝ] F} {P P_ : E}
    (hAdiff : ‖A - Aℚ‖ ≤ κ) (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - P_‖ ≤ κ) :
    ‖A P - Aℚ P_‖ ≤ 2 * κ + κ ^ 2 := by
  calc ‖A P - Aℚ P_‖
    _ = ‖(A P - Aℚ P) + (Aℚ P - Aℚ P_)‖ := by congr 1; abel
    _ ≤ ‖A P - Aℚ P‖ + ‖Aℚ P - Aℚ P_‖ := norm_add_le _ _
    _ = ‖(A - Aℚ) P‖ + ‖Aℚ (P - P_)‖ := by
        rw [ContinuousLinearMap.sub_apply, map_sub]
    _ ≤ ‖A - Aℚ‖ * ‖P‖ + ‖Aℚ‖ * ‖P - P_‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ κ * 1 + (1 + κ) * κ :=
        add_le_add
          (mul_le_mul hAdiff hP (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul hAℚnorm hPapprox (norm_nonneg _) (by norm_num [κ]))
    _ = 2 * κ + κ ^ 2 := by ring

/-- Variant of `clm_approx_apply_sub` for ‖P‖ ≤ 2, ‖P - P_‖ ≤ 2κ. -/
lemma clm_approx_apply_sub₂ {E F : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A Aℚ : E →L[ℝ] F} {P P_ : E}
    (hAdiff : ‖A - Aℚ‖ ≤ κ) (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ)
    (hP : ‖P‖ ≤ 2) (hPapprox : ‖P - P_‖ ≤ 2 * κ) :
    ‖A P - Aℚ P_‖ ≤ 4 * κ + 2 * κ ^ 2 := by
  calc ‖A P - Aℚ P_‖
    _ = ‖(A P - Aℚ P) + (Aℚ P - Aℚ P_)‖ := by congr 1; abel
    _ ≤ ‖A P - Aℚ P‖ + ‖Aℚ P - Aℚ P_‖ := norm_add_le _ _
    _ = ‖(A - Aℚ) P‖ + ‖Aℚ (P - P_)‖ := by
        rw [ContinuousLinearMap.sub_apply, map_sub]
    _ ≤ ‖A - Aℚ‖ * ‖P‖ + ‖Aℚ‖ * ‖P - P_‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ κ * 2 + (1 + κ) * (2 * κ) :=
        add_le_add
          (mul_le_mul hAdiff hP (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul hAℚnorm hPapprox (norm_nonneg _) (by norm_num [κ]))
    _ = 4 * κ + 2 * κ ^ 2 := by ring

/-- CLM with operator norm ≤ 1 preserves the unit ball. -/
lemma clm_unit_apply_le {E F : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A : E →L[ℝ] F} {x : E} (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1) : ‖A x‖ ≤ 1 :=
  (ContinuousLinearMap.le_opNorm A x).trans
    ((mul_le_mul hA hx (norm_nonneg _) (by linarith [norm_nonneg A])).trans (one_mul 1).le)

/-- Approximate image norm: ‖Aℚ P_‖ ≤ (1+κ)² from ‖Aℚ‖ ≤ 1+κ, ‖P‖ ≤ 1, ‖P-P_‖ ≤ κ. -/
lemma approx_image_norm_le {E F : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {Aℚ : E →L[ℝ] F} {P P_ : E}
    (hAℚnorm : ‖Aℚ‖ ≤ 1 + κ) (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - P_‖ ≤ κ) :
    ‖Aℚ P_‖ ≤ (1 + κ) * (1 + κ) :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul hAℚnorm (by linarith [norm_le_insert P P_]) (norm_nonneg _) (by norm_num [κ]))
