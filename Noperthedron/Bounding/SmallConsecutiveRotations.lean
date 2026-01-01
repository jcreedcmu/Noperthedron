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
  fin_cases d <;> simp [rot3, rot3_mat]

-- requires matrix form of Euler's rotation theorem
-- which in turn requires Schur decomposition
lemma rot3_rot3_orth_equiv_rotz {d d' : Fin 3} {α β : ℝ} :
    ∃ (u : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (γ : ℝ), γ ∈ Set.Ico (-π) π ∧
    rot3 d α ∘L rot3 d' β =
      u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap := by
  sorry

noncomputable abbrev tr := LinearMap.trace ℝ ℝ³
noncomputable abbrev tr' := LinearMap.trace ℝ (Fin 3 → ℝ)

lemma tr_rot3_rot3  {d d' : Fin 3} {α β : ℝ} : d ≠ d' → tr (rot3 d α ∘L rot3 d' β) = cos α + cos β + cos α * cos β := by
  intro d_ne_d'
  calc tr (rot3 d α ∘L rot3 d' β)
  _ = tr ((rot3_mat d α).toEuclideanLin.toContinuousLinearMap ∘L (rot3_mat d' β).toEuclideanLin.toContinuousLinearMap) := by simp [rot3_eq_rot3_mat_toEuclideanLin]
  _ = tr ((rot3_mat d α * rot3_mat d' β).toEuclideanLin) := by simp [Matrix.toEuclideanLin_eq_toLin, Matrix.toLin_mul (v₁:=?a) (v₂:=?a) (v₃:=?a)]
  _ = Matrix.trace (rot3_mat d α * rot3_mat d' β) := by simp only [Matrix.toEuclideanLin_eq_toLin, Matrix.trace_toLin_eq]
  _ = cos α + cos β + cos α * cos β := by
    fin_cases d <;> fin_cases d'
    all_goals try contradiction
    all_goals (simp [rot3_mat]; try ring_nf)

lemma tr_RzL {α : ℝ} : tr (RzL α) = 1 + 2 * Real.cos α :=
  calc tr (RzL α)
  _ = tr' ((Rz_mat α).toLin') := by simp [RzL, Matrix.toEuclideanLin_eq_toLin]
  _ = Matrix.trace (Rz_mat α) := by rw [Matrix.trace_toLin'_eq]
  _ = 1 + 2 * cos α := by
    simp [Matrix.trace, Fin.sum_univ_three]
    ring_nf

theorem norm_RxRy_minus_id_le_wlog {d d' : Fin 3} {α β : ℝ} :
    d ≠ d' → |α| ≤ 2 → |β| ≤ 2 → ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α^2 + β^2) := by
  intros d_ne_d' α_le β_le
  obtain ⟨u, γ, γ_in, rd_rd'_eq⟩ := rot3_rot3_orth_equiv_rotz (α:=α) (β:=β)
  rw [rd_rd'_eq]
  have h : |γ| ≤ √(α^2 + β^2) := by
    suffices cos √(α^2 + β^2) ≤ cos γ by
      apply le_of_not_gt
      intro h
      apply strictAntiOn_cos at h
      · by_cases γ_sign : 0 ≤ γ
        · rw [abs_of_nonneg] at h <;> linarith
        · rw [abs_of_neg, cos_neg] at h <;> linarith
      · simp only [Set.mem_Ico, Set.mem_Icc, sqrt_nonneg, true_and] at ⊢ γ_in
        apply sqrt_le_iff.mpr
        constructor
        · positivity
        · rw [←(sq_abs α), ←(sq_abs β)]
          grw [α_le, β_le]
          calc
          _ ≤ 3^2 := by norm_num
          _ ≤ π^2 := by simp only [sq_le_sq, Nat.abs_ofNat, pi_nonneg, abs_of_nonneg,
            pi_gt_three, le_of_lt]
      · simp only [Set.mem_Icc, abs_nonneg, abs_le, true_and]
        obtain ⟨le_γ, γ_lt⟩ := γ_in
        constructor <;> linarith

    suffices 2 * (1 + cos √(α^2 + β^2)) ≤ 2 * (1 + cos γ) by grind
    calc 2 * (1 + cos √(α^2 + β^2))
    _ ≤ (1 + cos α) * (1 + cos β) := by
      convert_to 2 + (2 * cos √(α ^ 2 + β ^ 2)) ≤ (1 + cos α) * (1 + cos β)
      · ring_nf
      apply one_plus_cos_mul_one_plus_cos_ge <;> assumption
    _ = (cos α + cos β + cos α * cos β) + 1 := by ring_nf
    _ = tr (rot3 d α ∘L rot3 d' β) + 1 := by rw [←(tr_rot3_rot3 d_ne_d')]
    _ = tr (u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap : ℝ³ →L[ℝ] ℝ³) + 1 := by rw [rd_rd'_eq]
    _ = tr (u.conj (RzL γ)) + 1 := by rfl
    _ = tr (RzL γ) + 1 := by rw [LinearMap.trace_conj']
    _ = 2 + 2 * cos γ := by rw [tr_RzL]; ring_nf
    _ = 2 * (1 + cos γ) := by ring_nf

  calc ‖u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap - 1‖
  _ = ‖u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap
        - (u.trans u.symm).toLinearIsometry.toContinuousLinearMap‖ := by
    rw [LinearIsometryEquiv.self_trans_symm]
    rfl
  _ = ‖u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap
        - u.toLinearIsometry.toContinuousLinearMap ∘L u.symm.toLinearIsometry.toContinuousLinearMap‖ := by
    congr
    reduce -- TODO: do this better
    simp only [LinearEquiv.invFun_eq_symm, LinearIsometryEquiv.coe_symm_toLinearEquiv,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
  _ = ‖u.toLinearIsometry.toContinuousLinearMap ∘L (RzL γ - 1) ∘L u.symm.toLinearIsometry.toContinuousLinearMap‖ := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    rfl
  _ = ‖RzL γ - 1‖ := by
    rw [LinearIsometry.norm_toContinuousLinearMap_comp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  _ = ‖RzC γ - 1‖ := by rfl
  _ ≤ ‖RzC γ - RzC 0‖ := by
    rw [RzC.map_zero_eq_one]
  _ ≤ ‖rot3 2 γ - rot3 2 0‖ := by rfl
  _ ≤ ‖γ‖ := by
      grw [dist_rot3_eq_dist_rot (d := 2), dist_rot2_le_dist, sub_zero]
  _ ≤ √(α^2 + β^2) := h

namespace PreferComp
  variable {R A B C : Type*}
  variable [Semiring R]
  variable [AddCommMonoid A] [Module R A] [TopologicalSpace A]
  variable [AddCommMonoid B] [Module R B] [TopologicalSpace B]
  variable [AddCommMonoid C] [Module R C] [TopologicalSpace C]
  def mul_eq_comp {f g : A →L[R] A} : g * f = g ∘L f := by rfl
  @[simp] def comp_image S (g : B →L[R] C) (f : A →L[R] B) : ⇑(g ∘L f) '' S = ⇑g '' (⇑f '' S) := by ext p; simp
end PreferComp

open PreferComp

theorem lemma12_2a {d d' : Fin 3} {α β : ℝ} (dne : d ≠ d') :
    ‖(rot3 d (2 * α)) ∘L (rot3 d' (2 * β)) - (rot3 d α) ∘L (rot3 d' β)‖  =
        ‖((rot3 d α) ∘L (rot3 d α)) ∘L ((rot3 d' β) ∘L (rot3 d' β)) - (rot3 d α) ∘L (rot3 d' β)‖  := by
  fin_cases d, d' <;> {
    try contradiction
    try simp only [rot3]
    try repeat rw [two_mul, AddChar.map_add_eq_mul, mul_eq_comp]
  }

theorem lemma12_2 {d d' : Fin 3} {α β : ℝ} :
    d ≠ d' → ‖rot3 d (2 * α) ∘L rot3 d' (2 * β) - 1‖ ≤ 2 * ‖rot3 d α ∘L rot3 d' β - 1‖ := by
    intro d_ne_d'
    calc
    _ = ‖(rot3 d (2 * α) ∘L rot3 d' (2 * β) - rot3 d α ∘L rot3 d' β) + (rot3 d α ∘L rot3 d' β - 1)‖ := by simp
    _ ≤ ‖rot3 d (2 * α) ∘L rot3 d' (2 * β) - rot3 d α ∘L rot3 d' β‖ + ‖rot3 d α ∘L rot3 d' β - 1‖ := by apply norm_add_le
    _ = ‖(rot3 d α ∘L rot3 d α) ∘L (rot3 d' β ∘L rot3 d' β) - rot3 d α ∘L rot3 d' β‖ + ‖rot3 d α ∘L rot3 d' β - 1‖ := by rw [lemma12_2a d_ne_d']
    _ ≤ ‖rot3 d α ∘L rot3 d' β - 1‖ + ‖rot3 d α ∘L rot3 d' β - 1‖ := by
      gcongr 1
      calc
        _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β) ∘L rot3 d' β - rot3 d α ∘L rot3 d' β‖ := by congr 1
        _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β) ∘L rot3 d' β - rot3 d α ∘L 1 ∘L rot3 d' β‖ := by congr 1
        _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β - 1) ∘L rot3 d' β‖ := by simp
        _ ≤ ‖(rot3 d α ∘L rot3 d' β - 1)‖ := by
          repeat grw [ContinuousLinearMap.opNorm_comp_le]
          repeat rw [lemma9]
          simp
    _ = 2 * ‖rot3 d α ∘L rot3 d' β - 1‖ := by ring

theorem lemma12_3 {d d' : Fin 3} {α β : ℝ} (n : ℕ) (d_ne_d' : d ≠ d') (α_in : |α| ≤ 2^(n+1)) (β_in : |β| ≤ 2^(n+1)) :
  ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α^2 + β^2) := by
    induction n generalizing α β with
    | zero => apply norm_RxRy_minus_id_le_wlog <;> grind
    | succ n' h =>
      calc ‖rot3 d α ∘L rot3 d' β - 1‖
        _ = ‖rot3 d (2 * (α / 2)) ∘L rot3 d' (2 * (β / 2)) - 1‖ := by
          field_simp
        _ ≤ 2 * ‖rot3 d (α / 2) ∘L rot3 d' (β / 2) - 1‖ := lemma12_2 d_ne_d'
        _ ≤ 2 * √((α / 2)^2 + (β / 2)^2) := by
          grw [h] <;> {
            simp only [abs_div, Nat.abs_ofNat]
            field_simp
            rw [pow_succ'] at α_in β_in
            assumption
          }
        _ = √(α^2 + β^2) := by
          field_simp
          rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by norm_num)]
          field_simp

theorem lemma12 {d d' : Fin 3} {α β : ℝ} (d_ne_d' : d ≠ d') :
  ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α^2 + β^2) := by
    let n : ℕ := Nat.clog 2 ⌈max |α| |β|⌉₊
    apply lemma12_3 n d_ne_d' <;> {
      unfold n
      rw [← Real.rpow_natCast, Nat.cast_add]
      simp only [Nat.cast_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Real.rpow_add_one,
        Real.rpow_natCast]
      calc
        _ ≤ max |α| |β| := by simp
        _ ≤ ⌈max |α| |β|⌉₊ := by apply Nat.le_ceil
        _ = ⌈max |α| |β|⌉₊ * 1 := by simp
        _ ≤ ⌈max |α| |β|⌉₊ * 2 := by gcongr; simp
        _ ≤ (2 ^ (Nat.clog 2 ⌈max |α| |β|⌉₊) : ℕ) * 2 := by
          gcongr
          apply Nat.le_pow_clog
          simp
        _ ≤ 2 ^ (Nat.clog 2 ⌈max |α| |β|⌉₊) * 2 := by simp
    }

theorem lemma12_equality_iff {d d' : Fin 3} {α β : ℝ} (d_ne_d' : d ≠ d') :
    ‖rot3 d α ∘L rot3 d' β - 1‖ = √(α^2 + β^2) ↔ (α = 0 ∧ β = 0) := by
  constructor
  · sorry
  · rintro ⟨hα, hβ⟩
    rw [hα, hβ]
    simp only [AddChar.map_zero_eq_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, sqrt_zero, norm_eq_zero]
    exact sub_self (ContinuousLinearMap.comp 1 1)


end Bounding
