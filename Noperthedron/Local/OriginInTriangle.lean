import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Local.Prelims

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

noncomputable section AristotleLemmas

/--
Determinant of two 2D vectors.
-/
def det2 (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0

/--
Relate determinant to inner product with rotated vector.
-/
lemma det2_eq_inner_rot (u v : EuclideanSpace ℝ (Fin 2)) : det2 u v = ⟪rotR (π/2) u, v⟫ := by
  -- By definition of determinant, we know that
  simp only [det2, Fin.isValue, rotR, rotR_mat, AddChar.coe_mk, Real.cos_pi_div_two,
    Real.sin_pi_div_two, LinearMap.coe_toContinuousLinearMap']
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Fin.isValue, Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.cons_mulVec,
    Matrix.cons_dotProduct, zero_mul, neg_mul, one_mul, Matrix.dotProduct_of_isEmpty, add_zero,
    zero_add, Matrix.empty_mulVec, star_trivial, Matrix.dotProduct_cons, mul_neg]
  ring!

/--
Identity relating three 2D vectors via determinants.
-/
lemma det2_identity (A B C : EuclideanSpace ℝ (Fin 2)) :
    (det2 B C) • A + (det2 C A) • B + (det2 A B) • C = 0 := by
  ext i
  fin_cases i
  · simp only [det2, Fin.isValue, Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.zero_apply]
    linarith
  · simp only [det2, Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.zero_apply]
    ring

/--
If the determinant of two 2D vectors is positive, they are linearly independent.
-/
lemma linear_independent_of_det2_pos (A B : EuclideanSpace ℝ (Fin 2)) (h : 0 < det2 A B) :
    LinearIndependent ℝ ![A, B] := by
  by_contra h_contra
  rw [linearIndependent_fin2] at h_contra
  -- If $c • B = A$ for some scalar $c$, then substituting into the determinant gives
  -- $det2 A B = A 0 * B 1 - A 1 * B 0 = (c • B) 0 * B 1 - (c • B) 1 * B 0 =
  -- c * (B 0 * B 1 - B 1 * B 0) = 0$, contradicting $h$.
  have h_contra' : ∀ c : ℝ, c • B = A → 0 = det2 A B := by
    intro c hc
    rw [← hc]
    unfold Local.det2
    ring_nf
    simp only [Fin.isValue, PiLp.smul_apply, smul_eq_mul, mul_comm]
    ring
  cases eq_or_ne B 0
  · simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, ne_eq, not_true_eq_false, smul_zero, Matrix.cons_val_zero,
      forall_const, false_and, not_false_eq_true]
    unfold Local.det2 at h
    norm_num at h
  · simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, ne_eq, not_false_eq_true, Matrix.cons_val_zero, true_and, not_forall,
      Decidable.not_not]
    linarith [h_contra' _ h_contra.choose_spec]

/--
If 0 is a strictly positive linear combination of three vectors A, B, C in R^2, and A, B are
linearly independent, then 0 is in the interior of their convex hull.
-/
lemma interior_triangle_of_pos_combo {A B C : EuclideanSpace ℝ (Fin 2)} (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_sum : a • A + b • B + c • C = 0)
    (h_indep : LinearIndependent ℝ ![A, B]) :
    0 ∈ interior (convexHull ℝ {A, B, C}) := by
  -- Since $A$ and $B$ are linearly independent, $A - C$ and $B - C$ are also linearly independent.
  have h_lin_ind : LinearIndependent ℝ ![A - C, B - C] := by
    have h_lin_comb : ∀ (x y : ℝ), x • (A - C) + y • (B - C) = 0 → x = 0 ∧ y = 0 := by
      intro x y hxy
      have h_lin_comb : (x + a / c * (x + y)) • A + (y + b / c * (x + y)) • B = 0 := by
        convert hxy using 1
        ext i
        have := congr(WithLp.ofLp $h_sum i)
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
                   PiLp.zero_apply] at this ⊢
        grind
      have := Fintype.linearIndependent_iff.mp h_indep
      have := this ![x + a / c * (x + y), y + b / c * (x + y)]
      simp_all [Fin.forall_fin_two]
      constructor <;> nlinarith only [div_mul_cancel₀ a hc.ne', div_mul_cancel₀ b hc.ne',
                                      this, hxy, ha, hb, hc]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i <;> simp [h_lin_comb _ _ (by simpa [ Fin.sum_univ_succ ] using hg )]
  -- Since $A - C$ and $B - C$ are linearly independent, the map
  -- $f(x, y) = x • (A - C) + y • (B - C) + C$ is an open map.
  have h_open_map : IsOpen (Set.image
      (fun p : ℝ × ℝ => p.1 • (A - C) + p.2 • (B - C) + C)
      { p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1 }) := by
    have h_open_map : IsOpenMap (fun p : ℝ × ℝ => p.1 • (A - C) + p.2 • (B - C)) := by
      have h_surjective :
          Function.Surjective (fun p : ℝ × ℝ => p.1 • (A - C) + p.2 • (B - C)) := by
        intro v
        obtain ⟨x, y, hx⟩ : ∃ x y : ℝ, v = x • (A - C) + y • (B - C) := by
          have h_basis : Submodule.span ℝ (Set.range ![A - C, B - C]) = ⊤ := by
            refine Submodule.eq_top_of_finrank_eq ?_
            rw [finrank_span_eq_card h_lin_ind]
            simp
          replace h_basis := Submodule.mem_span_range_iff_exists_fun ℝ |>.1
            (h_basis.symm ▸ Submodule.mem_top : v ∈ Submodule.span ℝ (Set.range ![A - C, B - C]))
          aesop
        aesop
      have h_open_map : ∀ (T : ℝ × ℝ →L[ℝ] Euc(2)), Function.Surjective T → IsOpenMap T := by
        exact fun T a ↦ ContinuousLinearMap.isOpenMap T a
      exact h_open_map (ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (A - C) +
                        ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (B - C))
                       h_surjective
    have h_open_map : IsOpen (Set.image
        (fun p : ℝ × ℝ => p.1 • (A - C) + p.2 • (B - C))
        { p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1 }) := by
      exact h_open_map _ (isOpen_Ioi.preimage continuous_fst |> IsOpen.inter <|
        isOpen_Ioi.preimage continuous_snd |> IsOpen.inter <|
          isOpen_lt (continuous_fst.add continuous_snd) continuous_const)
    convert h_open_map.preimage
      (show Continuous fun p : EuclideanSpace ℝ ( Fin 2 ) => p - C from
         continuous_id.sub continuous_const) using 1
    ext x
    grind
  refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (h_open_map.mem_nhds ?_) ?_)
  · refine ⟨⟨a / ( a + b + c ), b / ( a + b + c ) ⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      ring_nf
      exact ⟨by positivity, by positivity,
             by nlinarith [mul_inv_cancel₀ (by positivity : ( a + b + c ) ≠ 0)]⟩
    · convert congr((a + b + c) ⁻¹ • $h_sum) using 1
      · ext
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring_nf
        nlinarith [inv_mul_cancel_left₀ (by positivity : (a + b + c) ≠ 0) (C ‹_›)]
      · simp
  · simp only [convexHull_eq, Set.mem_insert_iff, Set.mem_singleton_iff, exists_and_left,
      Set.subset_def, Set.mem_image, Set.mem_setOf_eq, Prod.exists, forall_exists_index, and_imp]
    rintro x x₁ x₂ hx₁ hx₂ hx₃ rfl
    refine ⟨Fin 3, { 0, 1, 2 }, ![x₁, x₂, 1 - x₁ - x₂], ?_, by simp, ![A, B, C], by simp, ?_⟩
    · simp only [Fin.isValue, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
        Matrix.cons_val_zero, Matrix.cons_val_one, forall_eq, Matrix.cons_val, sub_nonneg]
      exact ⟨le_of_lt hx₁, le_of_lt hx₂, by linarith only [hx₃]⟩
    · simp only [Finset.centerMass, Fin.isValue, Finset.mem_insert, zero_ne_one,
        Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_insert,
        Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_singleton, Matrix.cons_val,
        add_sub_cancel, inv_one, smul_add, one_smul]
      ext
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
      ring

end AristotleLemmas

/-- [SY25] Lemma 26 -/
theorem origin_in_triangle {A B C : Euc(2)}
    (hA : 0 < ⟪rotR (π/2) A, B⟫) (hB : 0 < ⟪rotR (π/2) B, C⟫) (hC : 0 < ⟪rotR (π/2) C, A⟫) :
    0 ∈ interior (convexHull ℝ {A, B, C}) := by
  have h_linear_relation : (det2 B C) • A + (det2 C A) • B + (det2 A B) • C = 0 :=
    det2_identity A B C
  rw [← det2_eq_inner_rot] at hA hB hC
  exact interior_triangle_of_pos_combo
    (Local.det2 B C) (Local.det2 C A) (Local.det2 A B) hB hC hA h_linear_relation
    (linear_independent_of_det2_pos A B hA)
