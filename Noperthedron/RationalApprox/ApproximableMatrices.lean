import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.StarOrdered
import Noperthedron.RationalApprox.Lemma39
import Noperthedron.RationalApprox.TrigLemmas

namespace RationalApprox

inductive RewritableEntry : Type where
  | zero : RewritableEntry
  | one : RewritableEntry
  | minus_one : RewritableEntry
  | sin : RewritableEntry
  | cos : RewritableEntry
  | msin : RewritableEntry
  | mcos : RewritableEntry

def DistLeKappaEntry := RewritableEntry × RewritableEntry

@[simp]
noncomputable
def RewritableEntry.actual (z : ℝ) : RewritableEntry → ℝ
| .zero => 0
| .one => 1
| .minus_one => -1
| .sin => Real.sin z
| .cos => Real.cos z
| .msin => -Real.sin z
| .mcos => -Real.cos z

@[simp]
noncomputable
def DistLeKappaEntry.actual (dlke : DistLeKappaEntry) (x y : ℝ) :=
  dlke.fst.actual x * dlke.snd.actual y

@[simp]
noncomputable
def RewritableEntry.approx (z : ℝ) : RewritableEntry → ℝ
| .zero => 0
| .one => 1
| .minus_one => -1
| .sin => sinℚ z
| .cos => cosℚ z
| .msin => -sinℚ z
| .mcos => -cosℚ z

@[simp]
noncomputable
def DistLeKappaEntry.approx (dlke : DistLeKappaEntry) (x y : ℝ) :=
  dlke.fst.approx x * dlke.snd.approx y

noncomputable
def clinActual {m n : ℕ} (A : Matrix (Fin m) (Fin n) DistLeKappaEntry) (x y : ℝ) : E n →L[ℝ] E m :=
   A.map (·.actual x y) |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def clinApprox {m n : ℕ} (A : Matrix (Fin m) (Fin n) DistLeKappaEntry) (x y : ℝ) : E n →L[ℝ] E m :=
   A.map (·.approx x y) |>.toEuclideanLin.toContinuousLinearMap

section AristotleLemmas

/--
The actual value of any `RewritableEntry` (which can be 0, 1, -1, sin(z), cos(z), -sin(z), -cos(z))
is bounded by 1 in absolute value.
-/
theorem rewritable_entry_bound (e : RewritableEntry) (z : ℝ) :
    |e.actual z| ≤ 1 := by
  cases e <;> simp [RewritableEntry.actual, Real.abs_sin_le_one, Real.abs_cos_le_one]

/--
The error between the actual value and the rational approximation for any `RewritableEntry` is at
most `κ / 7` for inputs in `[-4, 4]`.
-/
theorem rewritable_entry_error (e : RationalApprox.RewritableEntry) (z : ℝ)
    (hz : z ∈ Set.Icc (-4 : ℝ) 4) : |e.actual z - e.approx z| ≤ κ / 7 := by
  rcases e with ( _ | _ | _ | _ | _ | _ | _ )
  all_goals
    simp [RewritableEntry.actual, RewritableEntry.approx]
  any_goals exact div_nonneg (by unfold RationalApprox.κ; norm_num) (by norm_num)
  · exact sinℚ_approx' z hz
  · exact cosℚ_approx' z hz
  · refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [abs_le.mp (sinℚ_approx' z hz)]
    · linarith [abs_le.mp (sinℚ_approx' z hz)]
  · convert cosℚ_approx' z hz using 1
    ring_nf
    rw [neg_add_eq_sub, abs_sub_comm]

/-
The error of the product of two `RewritableEntry` approximations is bounded by `2 * κ / 7 + κ^2 / 49`.
-/
theorem dist_le_kappa_entry_error (d : RationalApprox.DistLeKappaEntry) (x y : ℝ)
    (hx : x ∈ Set.Icc (-4 : ℝ) 4) (hy : y ∈ Set.Icc (-4 : ℝ) 4) :
    |d.actual x y - d.approx x y| ≤ 2 * κ / 7 + κ^2 / 49 := by
  -- Using the triangle inequality for the absolute value and the bounds from
  -- `rewritable_entry_bound` and `rewritable_entry_error`, we get:
  have h_abs (e1 e2 : RationalApprox.RewritableEntry) (x y : ℝ)
        (hx : x ∈ Set.Icc (-4 : ℝ) 4) (hy : y ∈ Set.Icc (-4 : ℝ) 4) :
        |e1.actual x * e2.actual y - e1.approx x * e2.approx y| ≤
        |e1.actual x| * |e2.actual y - e2.approx y| +
        |e1.actual x - e1.approx x| * |e2.approx y| := by
      rw [← abs_mul, ← abs_mul, mul_sub, sub_mul]
      exact abs_sub_le _ _ _
  -- Applying the bounds from `rewritable_entry_bound` and `rewritable_entry_error`, we get:
  have h_bound (e1 e2 : RationalApprox.RewritableEntry) (x y : ℝ)
        (hx : x ∈ Set.Icc (-4 : ℝ) 4) (hy : y ∈ Set.Icc (-4 : ℝ) 4) :
        |e1.actual x| ≤ 1 ∧ |e2.actual y| ≤ 1 ∧ |e1.approx x| ≤ 1 + κ / 7 ∧
        |e2.approx y| ≤ 1 + RationalApprox.κ / 7 := by
      have h_bound_e1 : |e1.actual x| ≤ 1 := rewritable_entry_bound e1 x
      have h_bound_e2 : |e2.actual y| ≤ 1 := rewritable_entry_bound e2 y
      have h_bound_e1_approx : |e1.approx x| ≤ 1 + RationalApprox.κ / 7 := by
        have := rewritable_entry_error e1 x hx
        rw [abs_le] at *
        constructor <;> linarith
      have h_bound_e2_approx : |e2.approx y| ≤ 1 + RationalApprox.κ / 7 := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · linarith [ abs_le.mp h_bound_e2, abs_le.mp ( rewritable_entry_error e2 y hy ) ]
        · linarith [ abs_le.mp h_bound_e2, abs_le.mp ( rewritable_entry_error e2 y hy ) ]
      exact ⟨h_bound_e1, h_bound_e2, h_bound_e1_approx, h_bound_e2_approx⟩
  -- Applying the bounds from `rewritable_entry_error`, we get:
  have h_error (e1 e2 : RewritableEntry) (x y : ℝ)
      (hx : x ∈ Set.Icc (-4 : ℝ) 4) (hy : y ∈ Set.Icc (-4 : ℝ) 4) :
      |e1.actual x - e1.approx x| ≤ RationalApprox.κ / 7 ∧
      |e2.actual y - e2.approx y| ≤ RationalApprox.κ / 7 := by
    exact ⟨rewritable_entry_error e1 x hx, rewritable_entry_error e2 y hy⟩
  refine le_trans (h_abs d.1 d.2 x y hx hy) ?_
  specialize h_bound d.1 d.2 x y hx hy
  specialize h_error d.1 d.2 x y hx hy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [
    abs_nonneg (RewritableEntry.actual x d.1),
    abs_nonneg (RewritableEntry.actual y d.2 - RewritableEntry.approx y d.2),
    abs_nonneg (RewritableEntry.actual x d.1 - RewritableEntry.approx x d.1),
    abs_nonneg (RewritableEntry.approx y d.2 ),
    show 0 ≤ κ by exact div_nonneg zero_le_one <| by norm_num]

/--
The error bound `3 * (2 * κ / 7 + κ^2 / 49)` is less than or equal to `κ`.
-/
theorem kappa_bound_aux : 3 * (2 * κ / 7 + κ^2 / 49) ≤ κ := by norm_num [κ]

end AristotleLemmas

/-- [SY25] Lemma 40 -/
theorem norm_matrix_actual_approx_le_kappa {m n : Finset.Icc 1 3}
    (A : Matrix (Fin m) (Fin n) DistLeKappaEntry) (x y : Set.Icc (-4 : ℝ) 4) :
    ‖clinActual A x y - clinApprox A x y‖ ≤ κ := by
  -- Let's choose δ as the upper bound from `dist_le_kappa_entry_error`.
  set δ := 2 * κ / 7 + κ^2 / 49 with hδ_def
  have hδ_pos : 0 < δ := by
    norm_num [ hδ_def, RationalApprox.κ ]
  have hδ_bound : ∀ i j, |(A.map (fun d => d.actual (x.val) (y.val)) i j) -
                          (A.map (fun d => d.approx (x.val) (y.val)) i j)| ≤ δ := by
    intro i j
    apply RationalApprox.dist_le_kappa_entry_error
    · exact x.prop
    · exact y.prop
  have h_sqrt_bound : Real.sqrt (m.val * n.val) ≤ 3 := by
    refine Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
    · positivity
    · norm_cast
      nlinarith [ Finset.mem_Icc.mp m.2, Finset.mem_Icc.mp n.2 ]
  -- Applying the norm bound from `norm_le_delta_sqrt_dims`.
  have norm_le_delta_sqrt_dims_applied :
      ‖(A.map (fun d => d.actual (x.val) (y.val)) -
        A.map (fun d => d.approx (x.val) (y.val))).toEuclideanLin.toContinuousLinearMap‖ ≤
      δ * Real.sqrt (m.val * n.val) := by
    convert norm_le_delta_sqrt_dims _ hδ_pos hδ_bound using 1
  refine le_trans ?_ ( norm_le_delta_sqrt_dims_applied.trans ?_)
  · simp_all [clinActual, clinApprox]
  · refine le_trans ( mul_le_mul_of_nonneg_left h_sqrt_bound <| by positivity ) ?_
    linarith [kappa_bound_aux]
