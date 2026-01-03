import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm
import Noperthedron.Bounding.RaRa
import Noperthedron.Bounding.Lemma11
import Noperthedron.Bounding.BoundingUtil
import Noperthedron.Bounding.OrthEquivRotz

/-!

Material for [SY25] Lemma 12.

-/

namespace Bounding
open Real
open scoped Real

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

section AristotleLemmas

/-
The squared norm of the difference between the composition of two rotations and the identity is related to the trace of the composition.
-/
theorem norm_rot3_comp_rot3_sq {d d' : Fin 3} {α β : ℝ} (h : d ≠ d') :
    ‖rot3 d α ∘L rot3 d' β - 1‖^2 = 3 - (Real.cos α + Real.cos β + Real.cos α * Real.cos β) := by
      -- Use `rot3_rot3_orth_equiv_rotz` to write the composition as `U RzL(γ) U⁻¹`.
      obtain ⟨u, γ, hγ, h_comp⟩ : ∃ (u : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (γ : ℝ), γ ∈ Set.Ico (-π) π ∧
        rot3 d α ∘L rot3 d' β =
          u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap := by
            exact rot3_rot3_orth_equiv_rotz;
      -- The norm is invariant under unitary conjugation, so ‖rot3 ... - 1‖ = ‖RzL γ - 1‖.
      have h_norm_inv : ‖(u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L u.symm.toLinearIsometry.toContinuousLinearMap) - 1‖ = ‖RzL γ - 1‖ := by
        have h_norm_inv : ∀ (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)), ‖u.toLinearIsometry.toContinuousLinearMap ∘L A ∘L u.symm.toLinearIsometry.toContinuousLinearMap‖ = ‖A‖ := by
          intro A;
          refine' le_antisymm _ _ <;> refine' ContinuousLinearMap.opNorm_le_bound _ _ _ <;> norm_num
          · intro x
            simpa [u.norm_map, u.symm.norm_map] using A.le_opNorm (u.symm x)
          · intro x
            have := ContinuousLinearMap.le_opNorm ( u.toLinearIsometry.toContinuousLinearMap.comp ( A.comp u.symm.toLinearIsometry.toContinuousLinearMap ) ) ( u x ) ; aesop;
        convert h_norm_inv ( RzL γ - 1 ) using 2 ; ext ; simp +decide [ sub_eq_add_neg ];
      -- We know ‖RzL γ - 1‖ = 2 |sin(γ/2)|, so ‖...‖^2 = 4 sin^2(γ/2) = 2(1 - cos γ).
      have h_norm_sq : ‖RzL γ - 1‖^2 = 2 * (1 - Real.cos γ) := by
        have h_norm_sq : ‖RzL γ - 1‖ = 2 * |Real.sin (γ / 2)| := by
          have := @Bounding.dist_rot3 2 γ 0; aesop;
        rw [h_norm_sq, mul_pow, sq_abs, Real.sin_sq, Real.cos_sq]
        ring_nf
      -- Also `tr (rot3 ...) = tr (RzL γ) = 1 + 2 cos γ`.
      have h_trace : tr (rot3 d α ∘L rot3 d' β) = 1 + 2 * Real.cos γ := by
        convert tr_RzL using 1
        convert LinearMap.trace_conj' _ _ using 2; aesop
      rw [ h_comp, h_norm_inv, h_norm_sq ]
      -- Substitute the trace into the equation.
      have h_subst : tr (rot3 d α ∘L rot3 d' β) = Real.cos α + Real.cos β + Real.cos α * Real.cos β := by
        exact tr_rot3_rot3 h
      linarith

end AristotleLemmas

theorem lemma12_equality_iff {d d' : Fin 3} {α β : ℝ} (d_ne_d' : d ≠ d') :
    ‖rot3 d α ∘L rot3 d' β - 1‖ = √(α^2 + β^2) ↔ (α = 0 ∧ β = 0) := by
  constructor
  · intro h_eq
    have h_eq_norm_sq : 3 - (Real.cos α + Real.cos β + Real.cos α * Real.cos β) =
                        α^2 + β^2 := by
      rw [←norm_rot3_comp_rot3_sq d_ne_d', h_eq, Real.sq_sqrt (by positivity)]
    have h_eq_cos_sq : 2 * (1 - Real.cos α) = α^2 ∧ 2 * (1 - Real.cos β) = β^2 := by
      have h_eq_cos_sq : 2 * (1 - Real.cos α) ≤ α^2 ∧ 2 * (1 - Real.cos β) ≤ β^2 := by
        have h_cos_ineq (x : ℝ) : 2 * (1 - Real.cos x) ≤ x^2 := by
          have h_trig (x : ℝ) : 2 * (1 - Real.cos x) = 4 * Real.sin (x / 2) ^ 2 := by
            rw [Real.sin_sq, Real.cos_sq]
            ring_nf
          rw [h_trig x, ←sq_abs]
          grw [abs_sin_le_abs]
          rw [sq_abs]
          linarith only
        exact ⟨h_cos_ineq α, h_cos_ineq β⟩
      constructor <;> nlinarith [sq_nonneg ( Real.cos α - 1 ), sq_nonneg ( Real.cos β - 1 ), Real.cos_sq' α, Real.cos_sq' β ]
    have h_eq_cos_sq : ∀ x : ℝ, 2 * (1 - Real.cos x) = x^2 → x = 0 := by
      intros x hx
      have h_cos_sq : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
        simpa only [Real.sin_sq, Real.cos_sq] using by ring_nf
      by_cases hx_zero : x = 0
      · exact hx_zero
      · have h_sin_sq : Real.sin (x / 2) ^ 2 < (x / 2) ^ 2 := by
          have h_sin_sq : ∀ y : ℝ, y ≠ 0 → Real.sin y ^ 2 < y ^ 2 := by
            exact fun y a ↦ sin_sq_lt_sq a
          exact h_sin_sq _ ( div_ne_zero hx_zero two_ne_zero );
        nlinarith [ mul_self_pos.mpr hx_zero ];
    exact ⟨ h_eq_cos_sq α ( by linarith ), h_eq_cos_sq β ( by linarith ) ⟩
  · rintro ⟨hα, hβ⟩
    rw [hα, hβ]
    simp only [AddChar.map_zero_eq_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, sqrt_zero, norm_eq_zero]
    exact sub_self (ContinuousLinearMap.comp 1 1)

end Bounding
