module

public import Noperthedron.PoseInterval
public import Noperthedron.RationalApprox.Basic

public section


/-!
# ℚ → ℝ cast bridges

Canonical lemmas connecting the rational world (`Fin n → ℚ` vectors,
`Matrix.toLin'` applications, `⬝ᵥ` dot products) to the real world
(`ℝⁿ` points via `toR2`/`toR3`, `toEuclideanLin` continuous linear maps,
`⟪·,·⟫` inner products).
-/

open scoped RealInnerProductSpace
open scoped Matrix

namespace RationalApprox

lemma cast_κℚ : ((κℚ : ℚ) : ℝ) = κ := by unfold κℚ κ; norm_num

lemma cast_Icc4_mem (a : Set.Icc (-4 : ℚ) 4) : (a : ℝ) ∈ Set.Icc (-4 : ℝ) 4 :=
  ⟨mod_cast a.property.1, mod_cast a.property.2⟩

lemma toR3_sub (v w : Fin 3 → ℚ) : toR3 (v - w) = toR3 v - toR3 w := by
  unfold toR3; ext i; simp

lemma toR2_sub (v w : Fin 2 → ℚ) : toR2 (v - w) = toR2 v - toR2 w := by
  unfold toR2; ext i; simp

/-- Cast of `Matrix.mulVec` over `ℚ` to `ℝ`. -/
lemma castℝ_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) :
    (fun i => ((M.mulVec v) i : ℝ)) =
      (M.map (fun x => (x : ℝ))).mulVec (fun i => (v i : ℝ)) := by
  ext i; push_cast [Matrix.mulVec, dotProduct]; rfl

lemma castℝ_dotProduct {n : ℕ} (v w : Fin n → ℚ) :
    ((v ⬝ᵥ w : ℚ) : ℝ) = (fun i => (v i : ℝ)) ⬝ᵥ (fun i => (w i : ℝ)) := by
  simp [dotProduct]

/-- The real inner product of casts equals the cast of the rational dot product. -/
lemma inner_toLp {n : ℕ} (v w : Fin n → ℚ) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (WithLp.toLp 2 (fun i => (v i : ℝ))) (WithLp.toLp 2 (fun i => (w i : ℝ))) =
    ((v ⬝ᵥ w : ℚ) : ℝ) := by
  have h := EuclideanSpace.inner_eq_star_dotProduct
    (WithLp.toLp 2 (fun i => (v i : ℝ)) : EuclideanSpace ℝ (Fin n))
    (WithLp.toLp 2 (fun i => (w i : ℝ)))
  simp only [star_trivial] at h
  rw [h, dotProduct_comm, ← castℝ_dotProduct]

lemma inner_toR3 (v w : Fin 3 → ℚ) :
    @inner ℝ ℝ³ _ (toR3 v) (toR3 w) = ((v ⬝ᵥ w : ℚ) : ℝ) := inner_toLp v w

lemma inner_toR2 (v w : Fin 2 → ℚ) :
    @inner ℝ ℝ² _ (toR2 v) (toR2 w) = ((v ⬝ᵥ w : ℚ) : ℝ) := inner_toLp v w

/-- The squared norm of a cast vector is the cast of the rational dot square. -/
lemma toLp_norm_sq_eq_dotProduct {n : ℕ} (v : Fin n → ℚ) :
    ‖(WithLp.toLp 2 (fun i => (v i : ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
      ((v ⬝ᵥ v : ℚ) : ℝ) := by
  rw [← inner_toLp v v]; exact (real_inner_self_eq_norm_sq _).symm

/-! ### Entrywise casts of the rational rotation matrices -/

lemma rotMℚ_mat_castℝ (θ φ : ℚ) :
    (rotMℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMℚ_mat, sinℚ_match, cosℚ_match]

lemma rotMθℚ_mat_castℝ (θ φ : ℚ) :
    (rotMθℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMθℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMθℚ_mat, sinℚ_match, cosℚ_match]

lemma rotMφℚ_mat_castℝ (θ φ : ℚ) :
    (rotMφℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMφℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMφℚ_mat, sinℚ_match, cosℚ_match]

lemma rotMθθℚ_mat_castℝ (θ φ : ℚ) :
    (rotMθθℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMθθℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMθθℚ_mat, sinℚ_match, cosℚ_match]

lemma rotMθφℚ_mat_castℝ (θ φ : ℚ) :
    (rotMθφℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMθφℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMθφℚ_mat, sinℚ_match, cosℚ_match]

lemma rotMφφℚ_mat_castℝ (θ φ : ℚ) :
    (rotMφφℚ_mat (θ : ℝ) (φ : ℝ)) = (rotMφφℚ_mat θ φ).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMφφℚ_mat, sinℚ_match, cosℚ_match]

lemma rotRℚ_mat_castℝ (α : ℚ) :
    (rotRℚ_mat (α : ℝ)) = (rotRℚ_mat α).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotRℚ_mat, sinℚ_match, cosℚ_match]

lemma rotR'ℚ_mat_castℝ (α : ℚ) :
    (rotR'ℚ_mat (α : ℝ)) = (rotR'ℚ_mat α).map (fun x => (x : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotR'ℚ_mat, sinℚ_match, cosℚ_match]

lemma toR3_vecXℚ (θ φ : ℚ) : toR3 (vecXℚ θ φ) = vecXℚℝ (↑θ : ℝ) ↑φ := by
  ext j; unfold toR3 vecXℚ vecXℚℝ
  fin_cases j <;> simp [sinℚ_match, cosℚ_match]

/-! ### Application bridges -/

/-- `toLp ∘ castℝ` intertwines a rational matrix-vector product with the
corresponding real `toEuclideanLin` application. -/
lemma toLp_cast_mulVec {m n : ℕ} {Mℚ : Matrix (Fin m) (Fin n) ℚ}
    {M : Matrix (Fin m) (Fin n) ℝ} (hM : M = Mℚ.map (fun x => (x : ℝ)))
    (v : Fin n → ℚ) :
    (WithLp.toLp 2 (fun i => ((Mℚ.mulVec v) i : ℝ)) : EuclideanSpace ℝ (Fin m)) =
      M.toEuclideanLin.toContinuousLinearMap (WithLp.toLp 2 (fun i => (v i : ℝ))) := by
  rw [castℝ_mulVec, ← hM]
  show WithLp.toLp 2 (M.mulVec _) =
    M.toEuclideanLin (WithLp.toLp 2 (fun i : Fin n => (v i : ℝ)))
  rw [Matrix.toLpLin_apply]

lemma toR2_rotMℚ_mat_mulVec (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMℚ_mat θ φ *ᵥ v) = rotMℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) :=
  toLp_cast_mulVec (rotMℚ_mat_castℝ θ φ) v

lemma toR2_rotMℚ (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMℚ θ φ v) = rotMℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) :=
  toLp_cast_mulVec (rotMℚ_mat_castℝ θ φ) v

lemma toR2_rotRℚ (α : ℚ) (v : Fin 2 → ℚ) :
    toR2 (rotRℚ α v) = rotRℚℝ (α : ℝ) (toR2 v) :=
  toLp_cast_mulVec (rotRℚ_mat_castℝ α) v

lemma toR2_rotM₂ℚ (p : Pose ℚ) (v : Fin 3 → ℚ) :
    toR2 (p.rotM₂ℚ v) = rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ) (toR3 v) :=
  toR2_rotMℚ p.θ₂ p.φ₂ v

lemma toR2_pose_rotM₂ℚ (p : Pose ℚ) (v : Fin 3 → ℚ) :
    toR2 (p.rotM₂ℚ v) = p.toReal.rotM₂ℚℝ (toR3 v) :=
  toR2_rotMℚ p.θ₂ p.φ₂ v

lemma toR2_pose_rotM₁ℚ (p : Pose ℚ) (v : Fin 3 → ℚ) :
    toR2 (p.rotM₁ℚ v) = p.toReal.rotM₁ℚℝ (toR3 v) :=
  toR2_rotMℚ p.θ₁ p.φ₁ v

lemma toR2_pose_rotRℚ (p : Pose ℚ) (v : Fin 2 → ℚ) :
    toR2 (p.rotRℚ v) = p.toReal.rotRℚℝ (toR2 v) :=
  toR2_rotRℚ p.α v

/-! ### Inner-product bridges for matrix applications -/

/-- One-matrix inner-product bridge:
`⟪M (toR3 v), toR2 w⟫ = ((Mℚ.mulVec v ⬝ᵥ w : ℚ) : ℝ)`. -/
lemma inner_one_bridge
    (Mℚ : Matrix (Fin 2) (Fin 3) ℚ) (M : Matrix (Fin 2) (Fin 3) ℝ)
    (hM : M = Mℚ.map (fun x => (x : ℝ)))
    (v : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ ℝ² _ (M.toEuclideanLin.toContinuousLinearMap (toR3 v)) (toR2 w) =
    ((Mℚ.mulVec v ⬝ᵥ w : ℚ) : ℝ) := by
  unfold toR3 toR2
  rw [← toLp_cast_mulVec hM v]
  exact inner_toLp _ _

/-- Two-matrix inner-product bridge for the `R ∘ M`-style composition. -/
lemma inner_two_bridge
    (Mℚ : Matrix (Fin 2) (Fin 2) ℚ) (Nℚ : Matrix (Fin 2) (Fin 3) ℚ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (N : Matrix (Fin 2) (Fin 3) ℝ)
    (hM : M = Mℚ.map (fun x => (x : ℝ))) (hN : N = Nℚ.map (fun x => (x : ℝ)))
    (v : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    @inner ℝ ℝ² _ (M.toEuclideanLin.toContinuousLinearMap
                     (N.toEuclideanLin.toContinuousLinearMap (toR3 v))) (toR2 w) =
    ((Mℚ.mulVec (Nℚ.mulVec v) ⬝ᵥ w : ℚ) : ℝ) := by
  unfold toR3 toR2
  rw [← toLp_cast_mulVec hN v, ← toLp_cast_mulVec hM (Nℚ.mulVec v)]
  exact inner_toLp _ _

end RationalApprox

end
