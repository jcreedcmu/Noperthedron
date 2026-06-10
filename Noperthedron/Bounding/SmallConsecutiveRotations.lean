import Mathlib.LinearAlgebra.Trace
import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm
import Noperthedron.Bounding.BoundingUtil
import Noperthedron.Bounding.OrthEquivRotz

/-!

Material for [SY25] Lemma 12.

-/

namespace Bounding
open Real

noncomputable abbrev tr := LinearMap.trace ℝ ℝ³
noncomputable abbrev tr' := LinearMap.trace ℝ (Fin 3 → ℝ)

lemma tr_rot3_rot3 {d d' : Fin 3} {α β : ℝ} : d ≠ d' → tr (rot3 d α ∘L rot3 d' β) = cos α + cos β + cos α * cos β := by
  intro d_ne_d'
  calc tr (rot3 d α ∘L rot3 d' β)
  _ = tr ((rot3_mat d α).toEuclideanLin.toContinuousLinearMap ∘L (rot3_mat d' β).toEuclideanLin.toContinuousLinearMap) := by simp [rot3_eq_rot3_mat_toEuclideanLin]
  _ = tr ((rot3_mat d α * rot3_mat d' β).toEuclideanLin) := by simp
  _ = Matrix.trace (rot3_mat d α * rot3_mat d' β) := by simp only [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
  _ = cos α + cos β + cos α * cos β := by
    fin_cases d <;> fin_cases d'
    all_goals try contradiction
    all_goals (simp [rot3_mat]; try ring_nf)

lemma tr_RzL {α : ℝ} : tr (RzL α) = 1 + 2 * Real.cos α :=
  calc tr (RzL α)
  _ = tr' ((Rz_mat α).toLin') := by simp [RzL, Matrix.toLpLin_eq_toLin]
  _ = Matrix.trace (Rz_mat α) := by rw [Matrix.trace_toLin'_eq]
  _ = 1 + 2 * cos α := by
    simp [Matrix.trace, Fin.sum_univ_three]
    ring_nf

section AristotleLemmas

/-
The squared norm of the difference between the composition of two rotations and the identity is related to the trace of the composition.
-/
theorem norm_rot3_comp_rot3_sq {d d' : Fin 3} {α β : ℝ} (h : d ≠ d') :
    ‖rot3 d α ∘L rot3 d' β - 1‖^2 = 3 - (Real.cos α + Real.cos β + Real.cos α * Real.cos β) := by
  obtain ⟨u, γ, _, h_comp⟩ := rot3_rot3_orth_equiv_rotz (α := α) (β := β) (d := d) (d' := d')
  have h_norm_conj (A : Euc(3) →L[ℝ] Euc(3)) :
      ‖u.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
       u.symm.toLinearIsometry.toContinuousLinearMap‖ = ‖A‖ := by
    rw [LinearIsometry.norm_toContinuousLinearMap_comp]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ u.symm
  have h_norm_eq : ‖(u.toLinearIsometry.toContinuousLinearMap ∘L RzL γ ∘L
      u.symm.toLinearIsometry.toContinuousLinearMap) - 1‖ = ‖RzL γ - 1‖ := by
    convert h_norm_conj (RzL γ - 1) using 2; ext; simp [sub_eq_add_neg]
  have h_norm_sq : ‖RzL γ - 1‖^2 = 2 * (1 - Real.cos γ) := by
    have h_norm : ‖RzL γ - 1‖ = 2 * |Real.sin (γ / 2)| := by
      have := @Bounding.dist_rot3 2 γ 0; aesop
    rw [h_norm, mul_pow, sq_abs, Real.sin_sq, Real.cos_sq]; ring_nf
  have h_trace : tr (rot3 d α ∘L rot3 d' β) = 1 + 2 * Real.cos γ := by
    convert tr_RzL using 1
    convert LinearMap.trace_conj' _ _ using 2; aesop
  rw [h_comp, h_norm_eq, h_norm_sq]
  linarith [tr_rot3_rot3 (α := α) (β := β) h, h_trace]

end AristotleLemmas

lemma two_mul_one_sub_cos_le (x : ℝ) : 2 * (1 - Real.cos x) ≤ x^2 := by
  have h_trig (x : ℝ) : 2 * (1 - Real.cos x) = 4 * Real.sin (x / 2) ^ 2 := by
    rw [Real.sin_sq, Real.cos_sq]
    ring_nf
  rw [h_trig x, ←sq_abs]
  grw [abs_sin_le_abs]
  rw [sq_abs]
  linarith only

lemma two_mul_one_sub_cos_eq_imp {x : ℝ} (hx : 2 * (1 - Real.cos x) = x^2) : x = 0 := by
  by_contra hx_zero
  have h_cos_sq : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    rw [Real.sin_sq, Real.cos_sq]; ring_nf
  linarith [sin_sq_lt_sq (div_ne_zero hx_zero two_ne_zero)]

theorem lemma12 {d d' : Fin 3} {α β : ℝ} (d_ne_d' : d ≠ d') :
  ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α^2 + β^2) := by
    have h := norm_rot3_comp_rot3_sq (α := α) (β := β) d_ne_d'
    have hle : ‖rot3 d α ∘L rot3 d' β - 1‖^2 ≤ α^2 + β^2 := by
      rw [h]
      have h2 : 0 ≤ (1 - Real.cos α) * (1 - Real.cos β) :=
        mul_nonneg (sub_nonneg.mpr (Real.cos_le_one α)) (sub_nonneg.mpr (Real.cos_le_one β))
      have h3 : 3 - (Real.cos α + Real.cos β + Real.cos α * Real.cos β) =
          2 * (1 - Real.cos α) + 2 * (1 - Real.cos β) - (1 - Real.cos α) * (1 - Real.cos β) := by
        ring
      linarith [two_mul_one_sub_cos_le α, two_mul_one_sub_cos_le β]
    calc ‖rot3 d α ∘L rot3 d' β - 1‖
        = √(‖rot3 d α ∘L rot3 d' β - 1‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(α^2 + β^2) := Real.sqrt_le_sqrt hle

theorem lemma12_equality_iff {d d' : Fin 3} {α β : ℝ} (d_ne_d' : d ≠ d') :
    ‖rot3 d α ∘L rot3 d' β - 1‖ = √(α^2 + β^2) ↔ (α = 0 ∧ β = 0) := by
  refine ⟨fun h_eq ↦ ?_, fun ⟨hα, hβ⟩ ↦ ?_⟩
  · have h1 : 3 - (Real.cos α + Real.cos β + Real.cos α * Real.cos β) = α^2 + β^2 := by
      rw [←norm_rot3_comp_rot3_sq d_ne_d', h_eq, Real.sq_sqrt (by positivity)]
    have h2 : 0 ≤ (1 - Real.cos α) * (1 - Real.cos β) :=
      mul_nonneg (by linarith [Real.cos_le_one α]) (by linarith [Real.cos_le_one β])
    have h3 : 3 - (Real.cos α + Real.cos β + Real.cos α * Real.cos β) =
        2 * (1 - Real.cos α) + 2 * (1 - Real.cos β) - (1 - Real.cos α) * (1 - Real.cos β) := by ring
    constructor <;> apply two_mul_one_sub_cos_eq_imp <;>
      linarith [two_mul_one_sub_cos_le α, two_mul_one_sub_cos_le β]
  · simp only [hα, hβ, AddChar.map_zero_eq_one, sq, mul_zero, add_zero, sqrt_zero, norm_eq_zero]
    exact sub_self (ContinuousLinearMap.comp 1 1)

end Bounding
