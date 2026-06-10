import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm

/-!

Material for [SY25] Lemma 10 and Lemma 12.

-/

namespace Bounding
open Real

theorem dist_rot3_apply {d : Fin 3} {α α' : ℝ} {v : ℝ³} :
  ‖(rot3 d α - rot3 d α') v‖ = 2 * |sin ((α - α') / 2)| * ‖(WithLp.toLp 2 (Fin.removeNth d v) : ℝ²)‖ := by
    let ix (i : Fin 3) : Fin 3 := match d, i with
      | 0,0 => 0
      | 0,1 => 1
      | 0,2 => 2
      | 1,0 => 1
      | 1,1 => 0
      | 1,2 => 2
      | 2,0 => 2
      | 2,1 => 0
      | 2,2 => 1
    fin_cases d <;>
    · try simp [rot3, RxC, RyC, RzC, RxL, RyL, RzL, Rx_mat, Ry_mat, Rz_mat, AddChar.coe_mk, ContinuousLinearMap.coe_sub',
        LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toLpLin_apply,
        Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue,
        WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
        PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, Matrix.transpose_apply,
        Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_one, mul_zero, add_zero,
        sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_neg, one_div,
        Fin.sum_univ_two]
      calc
        _ = ((v (ix 1) * cos α + -(v (ix 2) * sin α) - (v (ix 1) * cos α' + -(v (ix 2) * sin α'))) ^ 2 +
          (v (ix 1) * sin α + v (ix 2) * cos α - (v (ix 1) * sin α' + v (ix 2) * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ := by simp only [ix]
        _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v (ix 1) ^ 2 + v (ix 2) ^ 2)) ^ (2 : ℝ)⁻¹ := by
          have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
          refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
          calc
            _ = (v (ix 1) * cos α + -(v (ix 2) * sin α) - (v (ix 1) * cos α' + -(v (ix 2) * sin α'))) ^ 2 +
              (v (ix 1) * sin α + v (ix 2) * cos α - (v (ix 1) * sin α' + v (ix 2) * cos α')) ^ 2 := by simp [ix]
            _ = (v (ix 1) * (cos α - cos α') - v (ix 2) * (sin α - sin α')) ^ 2 +
                (v (ix 1) * (sin α - sin α') + v (ix 2) * (cos α - cos α')) ^ 2 := by ring_nf
            _ = 4 * (v (ix 1) ^ 2 + v (ix 2) ^ 2) * (sin ((α - α') / 2)) ^ 2 *
                ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
              simp [sin_sub_sin, cos_sub_cos, sq]
              ring_nf
            _ = 4 * (v (ix 1) ^ 2 + v (ix 2) ^ 2) * (sin ((α - α') / 2)) ^ 2 := by simp [sin_sq_add_cos_sq]
            _ = (2 * sin ((α - α') / 2)) ^ 2 * (v (ix 1) ^ 2 + v (ix 2) ^ 2) := by ring
        _ = 2 * |sin ((α - α') / 2)| * (v (ix 1) ^ 2 + v (ix 2) ^ 2) ^ (2 : ℝ)⁻¹ := by
          rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
          all_goals try positivity
          simp [sqrt_sq_eq_abs]

theorem dist_rot3 {d : Fin 3} {α α' : ℝ} :
  ‖rot3 d α - rot3 d α'‖ = 2 * |sin ((α - α') / 2)| := by
    refine ContinuousLinearMap.opNorm_eq_of_bounds ?_ ?_ ?_
    · positivity
    · intro v
      rw [dist_rot3_apply]
      gcongr
      simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
      apply rpow_le_rpow
      · positivity
      · fin_cases d <;> simp [Fin.removeNth_apply, Fin.succAbove] <;> positivity
      · positivity

    · intro N N_nonneg h
      let v : ℝ³ := if d = 0 then !₂[0, 1, 0] else !₂[1, 0, 0]
      have norm_v_one : ‖v‖ = 1 := by
        unfold v
        split <;> simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
      specialize h v
      calc
        2 * |sin ((α - α') / 2)| = ‖(rot3 d α - rot3 d α') v‖ := by
          rw [dist_rot3_apply]
          fin_cases d <;>
            simp [v, PiLp.norm_eq_sum, Fin.removeNth_apply, Fin.succAbove]
        _ ≤ N * ‖v‖ := h
        _ = N := by simp [norm_v_one]

/-- The difference of two rotations is a scalar multiple of a rotation. -/
lemma rotR_sub_rotR (α α' : ℝ) :
    rotR α - rotR α' = (2 * sin ((α - α') / 2)) • rotR ((α + α') / 2 + π / 2) := by
  ext v i
  fin_cases i <;>
    simp [rotR, rotR_mat, AddChar.coe_mk, Matrix.toLpLin_apply,
      Matrix.vecHead, Matrix.vecTail, cos_add_pi_div_two, sin_add_pi_div_two]
  · linear_combination v.ofLp 0 * cos_sub_cos α α' - v.ofLp 1 * sin_sub_sin α α'
  · linear_combination v.ofLp 0 * sin_sub_sin α α' + v.ofLp 1 * cos_sub_cos α α'

theorem dist_rotR {α α' : ℝ} : ‖rotR α - rotR α'‖ = 2 * |sin ((α - α') / 2)| := by
  rw [rotR_sub_rotR, norm_smul, rotR_norm_one, mul_one, Real.norm_eq_abs, abs_mul, abs_two]

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

def rot3_eq_rot3_mat_toEuclideanLin {d : Fin 3} {θ : ℝ}: rot3 d θ = (rot3_mat d θ).toEuclideanLin := by
  fin_cases d <;> simp [RxL, RyL, RzL, rot3, rot3_mat]

end Bounding
