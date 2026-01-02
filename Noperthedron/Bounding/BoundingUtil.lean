import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm
import Noperthedron.Bounding.RaRa
import Noperthedron.Bounding.Lemma11

/-!

Material for [SY25] Lemma 12.

-/

namespace Bounding
open Real
open scoped Real

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
        LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toEuclideanLin_apply,
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
            _ = (v (ix 1) * (cos α - cos α') - v (ix 2) * (sin α - sin α')) ^ 2 + (v (ix 1) * (sin α - sin α') + v (ix 2) * (cos α - cos α')) ^ 2 := by ring_nf
            _ = 4 * (v (ix 1) ^ 2 + v (ix 2) ^ 2) * (sin ((α - α') / 2)) ^ 2 * ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
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
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    try positivity
    · intro v
      rw [dist_rot3_apply]
      by_cases h : |sin ((α - α') / 2)| = 0
      · rw [h]; simp
      · field_simp
        simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
        apply rpow_le_rpow
        · positivity
        ·  try fin_cases d <;> {
            simp [Fin.removeNth_apply, Fin.succAbove] -- TODO: simp only
            positivity
          }
        · positivity

    · intro N N_nonneg h
      let d' := d
      let v : ℝ³ := if d = 0 then !₂[0, 1, 0] else !₂[1, 0, 0]
      have norm_v_one : ‖v‖ = 1 := by
        unfold v
        split <;> simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
      fin_cases d <;> {
        specialize h v
        calc
          2 * |sin ((α - α') / 2)| = _ := by rfl
          _ = ‖(rot3 d' α - rot3 d' α') v‖ := by
            rw [dist_rot3_apply]
            simp [v, d', PiLp.norm_eq_sum, Fin.removeNth_apply, Fin.succAbove, Fin.tail]
          _ ≤ N * ‖v‖ := by assumption
          _ = N := by simp [norm_v_one]
      }

theorem dist_rot2_apply {α α' : ℝ} {v : ℝ²} :
  ‖(rot2 α - rot2 α') v‖ = 2 * |sin ((α - α') / 2)| * ‖v‖ := by
    simp only [rot2, rot2_mat, AddChar.coe_mk, ContinuousLinearMap.coe_sub',
      LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_two, Fin.isValue,
      WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, Matrix.transpose_apply,
      Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_neg, one_div]
    calc
      ((v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
        (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ = _ := by rfl
      _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2)) ^ (2 : ℝ)⁻¹ := by
        have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
        refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
        calc
          (v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
            (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2 = _ := by rfl
          _ = (v 0 * (cos α - cos α') - v 1 * (sin α - sin α')) ^ 2 + (v 0 * (sin α - sin α') + v 1 * (cos α - cos α')) ^ 2 := by ring_nf
          _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 * ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
            simp only [Fin.isValue, cos_sub_cos, neg_mul, mul_neg, sin_sub_sin, sq]
            ring_nf
          _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 := by simp [sin_sq_add_cos_sq]
          _ = (2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
      _ = 2 * |sin ((α - α') / 2)| * (v 0 ^ 2 + v 1 ^ 2) ^ (2 : ℝ)⁻¹ := by
        rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
        all_goals try positivity
        simp only [Fin.isValue, sqrt_sq_eq_abs, abs_mul, Nat.abs_ofNat, rpow_one, one_div]

theorem dist_rot2 {α α' : ℝ} :
    ‖rot2 α - rot2 α'‖ = 2 * |sin ((α - α') / 2)| := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds ?_ ?_ ?_
  · positivity
  · intro v
    rw [dist_rot2_apply]
  · intro N N_nonneg h
    specialize h !₂[1, 0]
    have norm_xhat_eq_one : ‖!₂[(1 : ℝ), 0]‖ = 1 := by simp [PiLp.norm_eq_sum, Fin.sum_univ_two]
    calc
      2 * |sin ((α - α') / 2)| = _ := by rfl
      _ = ‖(rot2 α - rot2 α') !₂[(1 : ℝ), 0]‖ := by simp only [dist_rot2_apply, norm_xhat_eq_one, mul_one]
      _ ≤ N * ‖!₂[(1 : ℝ), 0]‖ := by assumption
      _ = N := by simp [norm_xhat_eq_one]

theorem dist_rot3_eq_dist_rot {d : Fin 3} {α α' : ℝ} : ‖rot3 d α - rot3 d α'‖ = ‖rot2 α - rot2 α'‖ := by
  simp only [dist_rot3, dist_rot2]

lemma two_mul_abs_sin_half_le {α : ℝ} : 2 * |sin (α / 2)| ≤ |α| := by
  have h : |sin (α / 2)| ≤ |α / 2| := abs_sin_le_abs
  calc
    2 * |sin (α / 2)| = _ := by rfl
    _ ≤ 2 * |α / 2| := by simp [h]
    _ = 2 * (|α| / 2) := by simp [abs_div]
    _ = |α| := by field

theorem dist_rot2_le_dist {α α' : ℝ} : ‖rot2 α - rot2 α'‖ ≤ ‖α - α'‖ := by
  calc
    ‖rot2 α - rot2 α'‖ = _ := by rfl
    _ = 2 * |sin ((α - α') / 2)| := by apply dist_rot2
    _ ≤ |α - α'| := by apply two_mul_abs_sin_half_le

def rot3_eq_rot3_mat_toEuclideanLin {d : Fin 3} {θ : ℝ}: rot3 d θ = (rot3_mat d θ).toEuclideanLin := by
  fin_cases d <;> simp [RxL, RyL, RzL, rot3, rot3_mat]

end Bounding
