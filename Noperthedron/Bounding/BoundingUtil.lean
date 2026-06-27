import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm

/-!

Material for [SY25] Lemma 10 and Lemma 12.

-/

namespace Bounding
open Real

/-- The difference of two rotation matrices is a scalar multiple of a rotation matrix. -/
lemma rotR_mat_sub_rotR_mat (α α' : ℝ) :
    rotR_mat α - rotR_mat α' = (2 * sin ((α - α') / 2)) • rotR_mat ((α + α') / 2 + π / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotR_mat, Fin.zero_eta, Fin.isValue, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, cos_add_pi_div_two,
      sin_add_pi_div_two, Matrix.smul_apply, smul_eq_mul, mul_neg, Fin.mk_one,
      Matrix.cons_val_one, sub_neg_eq_add]
  · linear_combination cos_sub_cos α α'
  · linear_combination -sin_sub_sin α α'
  · linear_combination sin_sub_sin α α'
  · linear_combination cos_sub_cos α α'

/-- The difference of two rotations is a scalar multiple of a rotation. -/
lemma rotR_sub_rotR (α α' : ℝ) :
    rotR α - rotR α' = (2 * sin ((α - α') / 2)) • rotR ((α + α') / 2 + π / 2) := by
  have e : ∀ θ, (rotR θ : ℝ² →L[ℝ] ℝ²) = (rotR_mat θ).toEuclideanLin.toContinuousLinearMap :=
    fun _ => rfl
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.toEuclideanLin.toContinuousLinearMap)
    (rotR_mat_sub_rotR_mat α α')
  simp only [map_sub, map_smul] at h
  rw [e, e, e]
  exact h

theorem dist_rotR {α α' : ℝ} : ‖rotR α - rotR α'‖ = 2 * |sin ((α - α') / 2)| := by
  rw [rotR_sub_rotR, norm_smul, rotR_norm_one, mul_one, Real.norm_eq_abs, abs_mul, abs_two]

/-- The diagonal matrix of the projection onto the coordinate plane perpendicular to axis `d`. -/
noncomputable def projPerp_mat (d : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun i => if i = d then 0 else 1

/-- The orthogonal projection of `ℝ³` onto the coordinate plane perpendicular to axis `d`. -/
noncomputable def projPerpL (d : Fin 3) : ℝ³ →L[ℝ] ℝ³ :=
  (projPerp_mat d).toEuclideanLin.toContinuousLinearMap

lemma projPerpL_apply (d : Fin 3) (v : ℝ³) (i : Fin 3) :
    projPerpL d v i = if i = d then 0 else v i := by
  simp [projPerpL, projPerp_mat, Matrix.mulVec_diagonal, ite_mul]

lemma projPerpL_norm_one (d : Fin 3) : ‖projPerpL d‖ = 1 := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun v => ?_) (fun N _ h => ?_)
  · rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [projPerpL_apply]
    split
    · simpa using sq_nonneg _
    · exact le_rfl
  · obtain ⟨j, hj⟩ := exists_ne d
    have h2 : projPerpL d (EuclideanSpace.single j 1) = EuclideanSpace.single j 1 := by
      ext i
      rw [projPerpL_apply]
      rcases eq_or_ne i d with rfl | hi
      · simp [hj.symm]
      · simp [hi]
    have h1 := h (EuclideanSpace.single j 1)
    rw [h2] at h1
    simpa using h1

/-- The difference of two rotation matrices about axis `d` is a scalar multiple of a rotation
matrix times the projection onto the plane of rotation. -/
lemma rot3_mat_sub_rot3_mat (d : Fin 3) (α α' : ℝ) :
    rot3_mat d α - rot3_mat d α' =
      (2 * sin ((α - α') / 2)) • (rot3_mat d ((α + α') / 2 + π / 2) * projPerp_mat d) := by
  fin_cases d
  all_goals (
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rot3_mat, Rx_mat, Fin.zero_eta, Fin.isValue, Matrix.sub_apply, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, sub_self,
        cos_add_pi_div_two, sin_add_pi_div_two, projPerp_mat, Matrix.cons_mul,
        Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.empty_mul, Equiv.symm_apply_apply,
        Matrix.smul_apply, Matrix.vecMul_diagonal, ↓reduceIte, mul_zero, smul_eq_mul,
        Fin.mk_one, Matrix.cons_val_one, one_ne_zero, mul_one, Fin.reduceFinMk,
        Matrix.cons_val, Fin.reduceEq, mul_neg, sub_neg_eq_add, Ry_mat, zero_ne_one,
        Rz_mat])
  · linear_combination cos_sub_cos α α'
  · linear_combination -sin_sub_sin α α'
  · linear_combination sin_sub_sin α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination -sin_sub_sin α α'
  · linear_combination sin_sub_sin α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination -sin_sub_sin α α'
  · linear_combination sin_sub_sin α α'
  · linear_combination cos_sub_cos α α'

theorem rot3_eq_rot3_mat_toEuclideanLin {d : Fin 3} {θ : ℝ} :
    rot3 d θ = (rot3_mat d θ).toEuclideanLin := by
  fin_cases d <;> simp [RxL, RyL, RzL, rot3, rot3_mat]

/-- The difference of two rotations about axis `d` is a scalar multiple of a rotation
composed with the projection onto the plane of rotation. -/
lemma rot3_sub_rot3 (d : Fin 3) (α α' : ℝ) :
    (rot3 d α : ℝ³ →L[ℝ] ℝ³) - rot3 d α' =
      (2 * sin ((α - α') / 2)) • ((rot3 d ((α + α') / 2 + π / 2) : ℝ³ →L[ℝ] ℝ³) ∘L projPerpL d) := by
  have hmul : ((rot3_mat d ((α + α') / 2 + π / 2) * projPerp_mat d).toEuclideanLin).toContinuousLinearMap
      = ((rot3_mat d ((α + α') / 2 + π / 2)).toEuclideanLin).toContinuousLinearMap ∘L projPerpL d := by
    ext v
    simp [projPerpL]
  have e : ∀ θ : ℝ, (rot3 d θ : ℝ³ →L[ℝ] ℝ³) = (rot3_mat d θ).toEuclideanLin.toContinuousLinearMap := by
    intro θ
    fin_cases d <;> rfl
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.toEuclideanLin.toContinuousLinearMap)
    (rot3_mat_sub_rot3_mat d α α')
  simp only [map_sub, map_smul, hmul] at h
  rw [e, e, e]
  exact h

theorem dist_rot3 {d : Fin 3} {α α' : ℝ} :
  ‖rot3 d α - rot3 d α'‖ = 2 * |sin ((α - α') / 2)| := by
    rw [rot3_sub_rot3, norm_smul, rot3_preserves_op_norm, projPerpL_norm_one, mul_one,
      Real.norm_eq_abs, abs_mul, abs_two]

theorem dist_rot3_eq_dist_rotR {d : Fin 3} {α α' : ℝ} :
    ‖rot3 d α - rot3 d α'‖ = ‖rotR α - rotR α'‖ := by
  rw [dist_rot3, dist_rotR]

/- [SY25] Lemma 10 -/

theorem norm_rotR_sub_rotR_lt {ε α α_ : ℝ} (hε : 0 < ε) (hα : |α - α_| ≤ ε) :
    ‖rotR α - rotR α_‖ < ε := by
  rw [dist_rotR]
  rcases eq_or_ne α α_ with rfl | hne
  · simpa using hε
  · have h := abs_sin_lt_abs (div_ne_zero (sub_ne_zero.mpr hne) two_ne_zero)
    rw [abs_div, abs_two] at h
    linarith

theorem norm_RxL_sub_RxL_eq {α α_ : ℝ} : ‖RxL α - RxL α_‖ = ‖rotR α - rotR α_‖ :=
  dist_rot3_eq_dist_rotR (d := 0)

theorem norm_RyL_sub_RyL_eq {α α_ : ℝ} : ‖RyL α - RyL α_‖ = ‖rotR α - rotR α_‖ :=
  dist_rot3_eq_dist_rotR (d := 1)

theorem norm_RzL_sub_RzL_eq {α α_ : ℝ} : ‖RzL α - RzL α_‖ = ‖rotR α - rotR α_‖ :=
  dist_rot3_eq_dist_rotR (d := 2)

end Bounding
