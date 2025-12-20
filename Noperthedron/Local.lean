import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Lemma23

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 21 -/
theorem pythagoras {θ φ : ℝ} (P : Euc(3)) :
    ‖rotM θ φ P‖ ^ 2 = ‖P‖ ^ 2 - ⟪vecX θ φ, P⟫ ^ 2 := by
  simp only [rotM, rotM_mat, neg_mul, LinearMap.coe_toContinuousLinearMap',
    EuclideanSpace.norm_sq_eq, Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.mulVec,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_dotProduct, Matrix.vecHead,
    Matrix.vecTail, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, Finset.univ_unique,
    Fin.default_eq_zero, Matrix.cons_val_succ, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, inner, vecX, RCLike.inner_apply, Real.ringHom_apply]
  grind [Real.sin_sq]

/-- [SY25] Lemma 24 -/
theorem abs_sub_inner_bars_le {n : ℕ} (A B A_ B_ : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, B P₂⟫ - ⟪A_ P₁, B_ P₂⟫| ≤
    ‖P₁‖ * ‖P₂‖ * (‖A - A_‖ * ‖B_‖ + ‖A_‖ * ‖B - B_‖ + ‖A - A_‖ * ‖B - B_‖) := by
  have h₁ := calc
    ⟪A P₁, B P₂⟫ = ⟪(A - A_) P₁ + A_ P₁, (B - B_) P₂ + B_ P₂⟫ := by simp
               _ = ⟪(A - A_) P₁, B_ P₂⟫ + ⟪A_ P₁, (B - B_) P₂⟫ +
                   ⟪(A - A_) P₁, (B - B_) P₂⟫ + ⟪A_ P₁, B_ P₂⟫ :=
                 by simp only [inner_add_left, inner_add_right]
                    ring
  -- Then the inequality follows from the triangle inequality,
  -- the Cauchy-Schwarz inequality and the submultiplicativity of ‖.‖:
  calc
    _ ≤ |⟪(A - A_) P₁, B_ P₂⟫| + |⟪A_ P₁, (B - B_) P₂⟫| + |⟪(A - A_) P₁, (B - B_) P₂⟫| :=
      by grind
    _ ≤ ‖(A - A_) P₁‖ * ‖B_ P₂‖ + ‖A_ P₁‖ * ‖(B - B_) P₂‖ + ‖(A - A_) P₁‖ * ‖(B - B_) P₂‖ :=
      by simp only [←Real.norm_eq_abs]
         grw [norm_inner_le_norm, norm_inner_le_norm, norm_inner_le_norm]
    _ ≤ _ :=
      by grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm,
              ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm]
         linarith only

/-- [SY25] Lemma 25 -/
theorem abs_sub_inner_le {n : ℕ} (A B : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤ ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (‖A‖ + ‖B‖ + ‖A - B‖) := by
  -- Exactly the same proof as the one for `abs_sub_inner_bars_le` yields:
  have h₁ : |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤
      ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (2 * ‖B‖ + ‖A - B‖) := by
    grind [abs_sub_inner_bars_le]
  -- Exchanging A and B, however, also gives the same inequality with 2 * ‖A‖ instead
  -- of 2 * ‖B‖.
  have h₂ : |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤
      ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (2 * ‖A‖ + ‖A - B‖) := by
    simp only [norm_sub_rev A B, abs_sub_comm ⟪A P₁, A P₂⟫ ⟪B P₁, B P₂⟫]
    grind [abs_sub_inner_bars_le]
  -- Taking the arithmetic mean of these two upper bounds produces the desired
  -- symmetric inequality.
  grind

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
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
        ring_nf
        have := congr(WithLp.ofLp $h_sum i)
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at this
        rw [show C i = -(a * A i + b * B i) / c by rw [eq_div_iff hc.ne']; linarith only [this]]
        ring
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

def Triangle : Type := Fin 3 → ℝ³

/-- The triangle P is congruent to Q in the usual geometric sense -/
def Triangle.Congruent (P Q : Triangle) : Prop := by
  sorry

/-- [SY25] Definition 27. Note that the "+ 1" at the type Fin 3 wraps. -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℝ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) < ⟪rotR (π / 2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫

/-- [SY25] Lemma 28 -/
theorem vecX_spanning {ε θ θ_ φ φ_ : ℝ} (P : Triangle)
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hSpanning: P.Spanning θ_ φ_ ε)
    (hX : ∀ i, 0 < ⟪vecX θ φ, P i⟫) :
    vecX θ φ ∈ Spanp P := by
  sorry

/-- [SY25] Lemma 30 -/
theorem inCirc {δ ε θ₁ θ₁_ θ₂ θ₂_ φ₁ φ₁_ φ₂ φ₂_ α α_: ℝ} {P Q : Euc(3)}
    (hε : 0 < ε)
    (hθ₁ : |θ₁ - θ₁_| ≤ ε) (hφ₁ : |φ₁ - φ₁_| ≤ ε)
    (hθ₂ : |θ₂ - θ₂_| ≤ ε) (hφ₂ : |φ₂ - φ₂_| ≤ ε)
    (hα : |α - α_| ≤ ε) :
    let T : Euc(2) := (1/2) • (rotR α_ (rotM θ₁_ φ₁_ P) + rotM θ₂_ φ₂_ Q)
    ‖T - rotM θ₂_ φ₂_ Q‖ ≤ δ →
    (rotR α (rotM θ₁ φ₁ P) ∈ Metric.ball T (δ + √5 * ε) ∧
     rotM θ₂ φ₂ Q ∈ Metric.ball T (δ + √5 * ε)) := by
  sorry

/-- The intersection of the δ-disc centered at Q with the interior of P -/
def sect (δ : ℝ) (Q : Euc(2)) (P : Finset Euc(2)) : Set Euc(2) := Metric.ball Q δ ∩ interior P

def LocallyMaximallyDistant (δ : ℝ) (Q Q_ : Euc(2)) (P : Finset Euc(2)) : Prop :=
  ∀ A ∈ sect δ Q_ P, ‖A‖ < ‖Q‖

theorem inner_ge_implies_LMD {P : Finset Euc(2)} {Q Q_ : Euc(2)} {δ r : ℝ}
    (hQ : Q ∈ P) (hQ_ : ‖Q - Q_‖ < δ) (hr : 0 < r) (hrQ : r < ‖Q‖)
    (hle : ∀ Pᵢ ∈ P \ {Q}, δ / r ≤ ⟪Q, Q - Pᵢ⟫ / (‖Q‖ * ‖Q - Pᵢ‖)) :
    LocallyMaximallyDistant δ Q Q_ P := by
  sorry

/-- [SY25] Lemma 33 -/
theorem coss {δ ε θ θ_ φ φ_ : ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    let M := rotM θ φ
    let M_ := rotM θ_ φ_
    (⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
     ((‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε))
    ≤
     ⟪M P, M (P - Q)⟫ / (‖M P‖ * ‖M (P - Q)‖):= by
  sorry

/--
Condition A_ε from [SY25] Theorem 36
-/
def Triangle.Aε (X : ℝ³) (P : Triangle) (ε : ℝ) : Prop :=
  ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ i : Fin 3, ⟪X, P i⟫ > ε * √2

noncomputable
def Triangle.Bε.lhs (i j : Fin 3) (Q : Triangle) (p : Pose) (ε : ℝ) : ℝ :=
   (⟪p.rotM₂ (Q i), p.rotM₂ (Q i - Q j)⟫ - 2 * ε * ‖Q i - Q j‖ * (ε + √2))
   / ((‖p.rotM₂ (Q i)‖ + ε * √2) * (‖p.rotM₂ (Q i - Q j)‖ + 2 * ε * √2))

/--
Condition B_ε from [SY25] Theorem 36
-/
def Triangle.Bε (Q : Triangle) (p : Pose) (ε δ r : ℝ) : Prop :=
  ∀ i j : Fin 3, i ≠ j →
  Triangle.Bε.lhs i j Q p ε > (δ + ε * √5) / r

instance : Membership Triangle (Finset ℝ³) where
  mem set tri := ∀ i : Fin 3, (tri i) ∈ set

/-- The condition on δ in the Local Theorem -/
def BoundDelta (δ : ℝ) (p : Pose) (P Q : Triangle) : Prop :=
  ∀ i : Fin 3, δ ≥ ‖p.rotR (p.rotM₁ (P i)) - p.rotM₂ (Q i)‖/2

/-- The condition on r in the Local Theorem -/
def BoundR (r ε : ℝ) (p : Pose) (Q : Triangle): Prop :=
  ∀ i : Fin 3, ‖p.rotM₂ (Q i)‖ > r + ε * √2

--- XXX: this is a leftover shim that should be cleaned up
noncomputable
def shape_of (S : Finset ℝ³) : Shape where
  vertices := S

-- TODO: Somehow separate out the "local theorem precondition"
-- predicate in a way that is suitable for the computational step's
-- tree check.
theorem local_theorem (P Q : Triangle)
    (cong_tri : P.Congruent Q)
    (poly : Finset ℝ³) (ne : poly.Nonempty)
    (hP : P ∈ poly) (hQ : Q ∈ poly)
    (radius_one : polyhedronRadius poly ne = 1)
    (p : Pose)
    (ε δ r : ℝ) (hε : ε > 0) (hr : r > 0)
    (hr : BoundR r ε p Q)
    (hδ : BoundDelta δ p P Q)
    (ae₁ : P.Aε p.vecX₁ ε) (ae₂ : Q.Aε p.vecX₂ ε)
    (span₁ : P.Spanning p.θ₁ p.φ₁ ε)
    (span₂ : Q.Spanning p.θ₂ p.φ₂ ε)
    (be : Q.Bε p ε δ r)
    : ∃ q ∈ p.closed_ball ε, RupertPose q (shape_of poly |>.hull) := by
  sorry
