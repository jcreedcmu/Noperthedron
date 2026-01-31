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
    simp only [rotMθ, clinActual, rotMθ_approx,
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
    simp only [rotMφ, clinActual, rotMφ_approx,
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
