import Mathlib.Analysis.Real.Pi.Bounds

/-!
 Proof of [SY25] Lemma 11, imported from https://github.com/badly-drawn-wizards/noperthedron.
-/

namespace Bounding

open Real

lemma one_add_cos_eq (a : ℝ) : 1 + cos a = 2 * cos (a / 2) ^ 2 := by
  rw [cos_sq]; field_simp

lemma lemma11_1_1 (a b : ℝ) : cos (√(a ^ 2 + b ^ 2) / 2) ^ 2 = cos (√((-a) ^ 2 + b ^ 2) / 2) ^ 2 := by simp
lemma lemma11_1_2 (a b : ℝ) : cos (√(a ^ 2 + b ^ 2) / 2) ^ 2 = cos (√(a ^ 2 + (-b) ^ 2) / 2) ^ 2 := by simp
lemma lemma11_1_3 (a b : ℝ) : cos (a / 2) ^ 2 * cos (b / 2) ^ 2 = cos ((-a) / 2) ^ 2 * cos (b / 2) ^ 2 := by simp only [neg_div, cos_neg]
lemma lemma11_1_4 (a b : ℝ) : cos (a / 2) ^ 2 * cos (b / 2) ^ 2 = cos (a / 2) ^ 2 * cos ((-b) / 2) ^ 2 := by simp only [neg_div, cos_neg]

lemma cosx_cosy_pos (a b : ℝ) (a_nonneg : 0 ≤ a) (a_le : a ≤ 2) (b_nonneg : 0 ≤ b) (b_le : b ≤ 2) :
    0 ≤ cos (a / 2) * cos (b / 2) := by
  have : 3 < π := pi_gt_three
  apply mul_nonneg <;> {
      apply cos_nonneg_of_mem_Icc
      constructor
      · linarith
      · linarith
    }

lemma cos_sqrt_pos (a b : ℝ) (a_nonneg : 0 ≤ a) (a_le : a ≤ 2) (b_nonneg : 0 ≤ b) (b_le : b ≤ 2) :
    0 ≤ cos √((a/2) ^ 2 + (b/2) ^ 2) := by
  apply cos_nonneg_of_mem_Icc
  refine ⟨by linarith [pi_pos, sqrt_nonneg ((a/2) ^ 2 + (b/2) ^ 2)], le_of_lt ?_⟩
  have h1 : (a / 2) ^ 2 ≤ 1 := (sq_le_one_iff₀ (by linarith)).mpr (by linarith)
  have h2 : (b / 2) ^ 2 ≤ 1 := (sq_le_one_iff₀ (by linarith)).mpr (by linarith)
  calc √((a / 2) ^ 2 + (b / 2) ^ 2) ≤ √2 := sqrt_le_sqrt (by linarith)
    _ < 3 / 2 := sqrt_two_lt_three_halves
    _ < π / 2 := by linarith [pi_gt_three]

noncomputable
def sin_sub_mul_cos (x : ℝ) : ℝ := sin x - x * cos x

lemma sin_sub_mul_cos_monotone_on : MonotoneOn sin_sub_mul_cos (Set.Icc 0 π) := by
  apply monotoneOn_of_deriv_nonneg
  · apply convex_Icc
  · apply Continuous.continuousOn
    unfold sin_sub_mul_cos
    continuity
  · unfold sin_sub_mul_cos
    fun_prop
  simp only [interior_Icc, Set.mem_Ioo]
  intro x x_in
  unfold sin_sub_mul_cos
  simp only [differentiableAt_sin, differentiableAt_fun_id, differentiableAt_cos,
    DifferentiableAt.fun_mul, deriv_fun_sub, Real.deriv_sin, deriv_fun_mul, deriv_id'', one_mul,
    deriv_cos', mul_neg, sub_add_cancel_left, neg_neg]
  have := sin_pos_of_mem_Ioo x_in
  rcases x_in with ⟨x_pos, x_lt⟩
  positivity

lemma sin_sub_mul_cos_nonneg (x : ℝ) : x ∈ Set.Icc 0 π → 0 ≤ sin_sub_mul_cos x := by
  simp only [Set.mem_Icc, and_imp]
  intro x_nonneg x_le
  calc
    0 = sin_sub_mul_cos 0 := by simp [sin_sub_mul_cos]
    _ ≤ sin_sub_mul_cos x := by
      apply sin_sub_mul_cos_monotone_on <;> (try simp only [Set.mem_Icc, le_refl, true_and]) <;> grind

lemma cos_sqrt_deriv {x : ℝ} (hx : x ∈ Set.Ioo 0 (π ^ 2)) : deriv (cos ∘ sqrt) x = -sin √x / (2 * √x) := by
  obtain ⟨x_pos, x_le⟩ := hx
  rw [deriv_comp _ differentiableAt_cos (DifferentiableAt.sqrt differentiableAt_fun_id x_pos.ne.symm)]
  rw [deriv_cos', deriv_sqrt differentiableAt_fun_id x_pos.ne.symm, deriv_id'']
  simp [field]

lemma sin_sqrt_deriv {x : ℝ} (hx : x ∈ Set.Ioo 0 (π ^ 2)) : deriv (sin ∘ sqrt) x = cos √x / (2 * √x) := by
  obtain ⟨x_pos, x_le⟩ := hx
  rw [show sin ∘ sqrt = fun x ↦ sin (sqrt x) by rfl]
  rw [_root_.deriv_sin (DifferentiableAt.sqrt differentiableAt_fun_id x_pos.ne.symm)]
  rw [deriv_sqrt differentiableAt_fun_id x_pos.ne.symm, deriv_id'']
  simp [field]

lemma convexOn_cos_sqrt : ConvexOn ℝ (Set.Icc 0 (π^2)) (cos ∘ sqrt) := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · fun_prop
  · refine DifferentiableOn.comp (t:=Set.univ) ?_ ?_ ?_
    · fun_prop
    · simp only [interior_Icc]
      apply DifferentiableOn.sqrt
      · fun_prop
      · grind
    · exact Set.mapsTo_univ _ _
  · simp only [interior_Icc]
    apply DifferentiableOn.congr (f := (-((sin ·) / (2 * ·)) ∘ sqrt))
    · simp only [differentiableOn_neg_iff]
      apply DifferentiableOn.comp (t:=Set.Ioi 0)
      · apply DifferentiableOn.div
        · fun_prop
        · fun_prop
        · grind
      · apply DifferentiableOn.sqrt
        · fun_prop
        · grind
      · apply Set.mapsTo_iff_subset_preimage.mpr
        simp only [Set.subset_def, Set.mem_Ioo, Set.mem_preimage, Set.mem_Ioi, sqrt_pos, and_imp]
        grind
    · intro x x_in
      simp only [Pi.neg_apply, Function.comp_apply, Pi.div_apply, ←neg_div]
      exact cos_sqrt_deriv x_in
  · simp only [interior_Icc, Set.mem_Ioo, Function.iterate_succ, Function.iterate_zero, Function.id_def,
    Function.comp_apply, and_imp]
    intro x x_pos x_lt
    rw [(Set.EqOn.deriv (_ : Set.EqOn (deriv (cos ∘ sqrt)) (fun y => -sin √y / (2 * √y)) (Set.Ioo 0 (π^2))) (by simp [Ioo_eq_ball] : IsOpen (Set.Ioo 0 (π^2))))]
    · rw [deriv_fun_div]
      · simp only [deriv.fun_neg', neg_mul, deriv_const_mul_field', sub_neg_eq_add]
        conv in (fun y => sin √y) =>
          change (sin ∘ sqrt)
        rw [sin_sqrt_deriv ⟨x_pos, x_lt⟩, deriv_sqrt differentiableAt_fun_id x_pos.ne.symm, deriv_id'']
        simp only [one_div, mul_inv_rev]
        field_simp; ring_nf
        rw [add_comm]
        apply sin_sub_mul_cos_nonneg
        simp only [Set.mem_Icc, sqrt_nonneg, sqrt_le_iff, true_and]
        refine ⟨pi_nonneg, ?_⟩
        linarith
      · simp only [differentiableAt_fun_neg_iff]
        apply DifferentiableAt.fun_comp'
        · simp
        apply DifferentiableAt.sqrt
        · simp
        linarith
      · apply DifferentiableAt.const_mul
        apply DifferentiableAt.sqrt
        · simp
        · linarith
      · positivity
    · grind
    · intro x; apply cos_sqrt_deriv

theorem one_plus_cos_mul_one_plus_cos_ge'' {a b : ℝ} (a_nonneg : 0 ≤ a) (a_le : a ≤ 2) (b_nonneg : 0 ≤ b) (b_le : b ≤ 2)
  (x y : ℝ) (ha : a / 2 = x) (hb: b / 2 = y) :
    2 * cos √(x ^ 2 + y ^ 2) ≤ 2 * cos x * cos y := by
  rw [two_mul_cos_mul_cos]
  let f := cos ∘ sqrt
  calc
    2 * cos √(x ^ 2 + y ^ 2) = _ := by rfl
    _ = 2 * f (x ^ 2 + y ^ 2) := by rfl
    _ = 2 * f (1/2 * (x - y)^2 + 1/2 * (x + y)^2) := by ring_nf
    _ ≤ 2 * (1/2 * f ((x - y)^2) + 1/2 * f ((x + y)^2)) := by
      subst ha hb
      simp only [mul_le_mul_iff_right₀, Nat.ofNat_pos]
      apply convexOn_cos_sqrt.2
      · simp
        constructor
        · positivity
        · apply sq_le_sq.mpr
          field_simp
          simp only [abs_div, Nat.abs_ofNat]
          field_simp
          apply le_of_lt
          calc
            |a - b| = _ := by rfl
            _ ≤ |a| + |b| := by apply abs_sub
            _ ≤ 2 * 3 := by (repeat rw [abs_of_nonneg]) <;> linarith
            _ < 2 * π := by simp [pi_gt_three]
            _ = 2 * |π| := by rw [abs_of_nonneg] ; positivity
      · simp
        constructor
        · positivity
        · apply sq_le_sq.mpr
          repeat rw [abs_of_nonneg]
          · field_simp
            apply le_of_lt
            calc
              a + b = _ := by rfl
              _ ≤ 2 * 3 := by linarith
              _ < 2 * π := by simp [pi_gt_three]
          · positivity
          · positivity
      · positivity
      · positivity
      · ring
    _ = f ((x - y)^2) + f ((x + y)^2) := by field_simp
    _ = cos √((x - y)^2) + cos √((x + y)^2) := by simp [f]
    _ = cos |x - y| + cos |x + y| := by simp [sqrt_sq_eq_abs]
    _ = cos (x - y) + cos (x + y) := by simp

theorem one_plus_cos_mul_one_plus_cos_ge' {a b : ℝ} (a_nonneg : 0 ≤ a) (a_le : a ≤ 2) (b_nonneg : 0 ≤ b) (b_le : b ≤ 2) :
    cos (√(a ^ 2 + b ^ 2) / 2) ^ 2 ≤ cos (a / 2) ^ 2 * cos (b / 2) ^ 2 := by
  have : √(a ^ 2 + b ^ 2) / 2 =  √((a / 2) ^ 2 + (b / 2) ^ 2) := by
    field_simp; simp; field_simp
  rw [this]
  generalize ha : a / 2 = x, hb : b / 2 = y
  rw [← mul_pow]
  apply sq_le_sq.mpr
  have hxy : 0 ≤ cos x * cos y := by rw [← ha, ← hb]; exact cosx_cosy_pos a b a_nonneg a_le b_nonneg b_le
  have hxy2 : 0 ≤ cos √(x ^ 2 + y ^ 2) := by rw [← ha, ← hb]; exact cos_sqrt_pos a b a_nonneg a_le b_nonneg b_le
  rw [abs_of_nonneg hxy, abs_of_nonneg hxy2]
  suffices hs : 2 * cos √(x ^ 2 + y ^ 2) ≤ 2 * cos x * cos y by
    field_simp at hs; assumption
  exact one_plus_cos_mul_one_plus_cos_ge'' a_nonneg a_le b_nonneg b_le x y ha hb

theorem one_plus_cos_mul_one_plus_cos_ge {a b : ℝ} (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    2 + 2 * Real.cos √(a ^ 2 + b ^ 2) ≤ (1 + Real.cos a) * (1 + Real.cos b) := by
  repeat rw [one_add_cos_eq]
  field_simp
  rw [one_add_cos_eq]
  field_simp
  change  cos (√(a ^ 2 + b ^ 2) / 2) ^ 2 ≤ cos (a / 2) ^ 2 * cos (b / 2) ^ 2
  revert ha hb
  simp only [abs_le, and_imp]
  intro le_a a_le le_b b_le
  by_cases a_sign : 0 ≤ a <;> by_cases b_sign : 0 ≤ b
  · exact one_plus_cos_mul_one_plus_cos_ge' a_sign a_le b_sign b_le
  · rw [lemma11_1_2, lemma11_1_4]
    apply one_plus_cos_mul_one_plus_cos_ge' <;> linarith
  · rw [lemma11_1_1, lemma11_1_3]
    apply one_plus_cos_mul_one_plus_cos_ge' <;> linarith
  · rw [lemma11_1_1, lemma11_1_2, lemma11_1_3, lemma11_1_4]
    apply one_plus_cos_mul_one_plus_cos_ge' <;> linarith

end Bounding
