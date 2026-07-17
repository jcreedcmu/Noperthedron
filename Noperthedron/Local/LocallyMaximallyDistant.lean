module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Noperthedron.Basic
public import Noperthedron.Local.Prelims

@[expose] public section


namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- The intersection of the δ-disc centered at Q with the interior of the convex hull of P -/
def sect (δ : ℝ) (Q : Euc(2)) (P : Finset Euc(2)) : Set Euc(2) :=
  Metric.ball Q δ ∩ interior (convexHull ℝ P)

/--
[SY25] Definition 31, simplified: the paper's "Q is δ-LMD with respect to Q_"
uses a ball around an auxiliary center Q_ with ‖Q - Q_‖ < δ, whose only role is
to bound ‖A - Q‖ < 2δ for A in that ball. We center the ball at Q itself, so
the radius here corresponds to the paper's 2δ.
-/
def LocallyMaximallyDistant (δ : ℝ) (Q : Euc(2)) (P : Finset Euc(2)) : Prop :=
  ∀ A ∈ sect δ Q P, ‖A‖ < ‖Q‖

/--
If P lies in the closed halfspace {x | ⟪Q, x⟫ ≤ ‖Q‖²}, then Q is not in the interior of the
convex hull of P: the hull also lies in the halfspace, whose interior is the open halfspace
{x | ⟪Q, x⟫ < ‖Q‖²}, and Q is on the bounding hyperplane.
-/
private lemma not_mem_interior_of_le_halfspace {P : Finset Euc(2)} {Q : Euc(2)}
    (hQ_ne_zero : Q ≠ 0) (h : ∀ y ∈ P, ⟪Q, y⟫ ≤ ‖Q‖ ^ 2) :
    Q ∉ interior (convexHull ℝ (P : Set Euc(2))) := by
  intro hQ_int
  have h_ne : innerSL ℝ Q ≠ 0 := fun h0 => hQ_ne_zero <| by
    simpa [inner_self_eq_zero] using congrFun (congrArg DFunLike.coe h0) Q
  have h_mem : Q ∈ interior (innerSL ℝ Q ⁻¹' Set.Iic (‖Q‖ ^ 2)) :=
    interior_mono
      (convexHull_min h (convex_halfSpace_le (innerSL ℝ Q).toLinearMap.isLinear _)) hQ_int
  rw [← ((innerSL ℝ Q).isOpenMap_of_ne_zero h_ne).preimage_interior_eq_interior_preimage
      (innerSL ℝ Q).continuous, interior_Iic] at h_mem
  simp at h_mem

/--
[SY25] Lemma 32, adapted to the Q-centered `LocallyMaximallyDistant`: the ball
of radius 2δ around Q contains the paper's ball of radius δ around any Q_ with
‖Q - Q_‖ < δ, and the cosine bound δ/r is unchanged.
-/
theorem inner_ge_implies_LMD {P : Finset Euc(2)} {Q : Euc(2)} {δ r : ℝ}
    (hQ : Q ∈ P) (hr : 0 < r) (hrQ : r < ‖Q‖)
    (hle : ∀ Pᵢ ∈ P, Pᵢ ≠ Q → δ / r ≤ ⟪Q, Q - Pᵢ⟫ / (‖Q‖ * ‖Q - Pᵢ‖)) :
    LocallyMaximallyDistant (2 * δ) Q P := by
  rintro A ⟨hA_ball, hA_int⟩
  rw [Metric.mem_ball, dist_eq_norm] at hA_ball
  have hδ_pos : 0 < δ := by linarith [norm_nonneg (A - Q)]
  have hQ_pos : 0 < ‖Q‖ := hr.trans hrQ
  -- Every vertex y satisfies ⟪Q, y⟫ + (δ/r)‖Q‖ ⋅ dist y Q ≤ ‖Q‖²: with equality for y = Q,
  -- and by the angle hypothesis for y ≠ Q.
  have h_vertex : ∀ y ∈ P, ⟪Q, y⟫ + δ / r * ‖Q‖ * dist y Q ≤ ‖Q‖ ^ 2 := by
    intro y hy
    rcases eq_or_ne y Q with rfl | hne
    · simp
    · have h1 := (le_div_iff₀ (mul_pos hQ_pos (norm_sub_pos_iff.mpr hne.symm))).mp (hle y hy hne)
      simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h1
      rw [dist_comm, dist_eq_norm]
      linarith
  -- The left-hand side is a convex function of y, so the bound extends to the convex hull.
  have h_convexOn : ConvexOn ℝ Set.univ fun x : Euc(2) => ⟪Q, x⟫ + δ / r * ‖Q‖ * dist x Q :=
    ((innerSL ℝ Q).toLinearMap.convexOn convex_univ).add
      ((convexOn_univ_dist Q).smul (by positivity))
  have h_hull : ∀ B ∈ convexHull ℝ (P : Set Euc(2)),
      ⟪Q, B⟫ + δ / r * ‖Q‖ * ‖B - Q‖ ≤ ‖Q‖ ^ 2 := by
    intro B hB
    obtain ⟨y, hy, hBy⟩ := h_convexOn.exists_ge_of_mem_convexHull (Set.subset_univ _) hB
    rw [← dist_eq_norm]
    exact hBy.trans (h_vertex y hy)
  -- A ≠ Q: dropping the nonnegative distance term from h_vertex puts P in the closed
  -- halfspace {x | ⟪Q, x⟫ ≤ ‖Q‖²}, so Q is not in the interior of the hull.
  have hA_ne_Q : A ≠ Q := by
    intro h_eq
    refine not_mem_interior_of_le_halfspace (norm_pos_iff.mp hQ_pos) (fun y hy => ?_)
      (h_eq ▸ hA_int)
    have h0 : 0 ≤ δ / r * ‖Q‖ * dist y Q := by positivity
    linarith [h_vertex y hy]
  have hAQ_pos : 0 < ‖A - Q‖ := norm_sub_pos_iff.mpr hA_ne_Q
  -- A is within 2δ of Q, and 2δ < 2(δ/r)‖Q‖ since r < ‖Q‖.
  have h2δ : 2 * δ < 2 * (δ / r) * ‖Q‖ :=
    calc 2 * δ = 2 * δ * 1 := (mul_one _).symm
      _ < 2 * δ * (‖Q‖ / r) := by
          exact mul_lt_mul_of_pos_left ((one_lt_div hr).mpr hrQ) (by positivity)
      _ = 2 * (δ / r) * ‖Q‖ := by ring
  -- Expand ‖A‖² = ‖Q + (A - Q)‖² and combine the bounds.
  have h_expand : ‖A‖ ^ 2 = ‖Q‖ ^ 2 + 2 * ⟪Q, A - Q⟫ + ‖A - Q‖ ^ 2 := by
    have h := norm_add_sq_real Q (A - Q)
    rwa [add_sub_cancel] at h
  have h_sq : ‖A‖ ^ 2 < ‖Q‖ ^ 2 := by
    have h3 : ‖A - Q‖ ^ 2 < 2 * (δ / r) * ‖Q‖ * ‖A - Q‖ := by
      rw [sq]
      exact mul_lt_mul_of_pos_right (hA_ball.trans h2δ) hAQ_pos
    have h_inner := h_hull A (interior_subset hA_int)
    simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h_expand
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg Q) h_sq

end Local
end
