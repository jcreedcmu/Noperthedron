/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationPartials.RotMOuter
import Noperthedron.Global.Basic
import Noperthedron.Global.SymbolicRotationOuter

/-!
# Second Partial Outer Lemmas

This file contains:
- `outer_second_partial_A` and `outer_third_partial_A` definitions, with norm bounds
  and permutation symmetries inherited from the generated symbolic tables;
- **`second_partial_rotproj_outer_eq`**, **`third_partial_rotproj_outer_eq`**: uniform
  instances of the outer symbolic bridge (`SymbolicRotation.iterPartialOuter_eval_eq`);
- **`third_partial_inner_rotM_outer`** and **`rotation_third_partials_bounded_outer`**.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## The A[i,j] table for outer second partials

For the outer function (2 variables: θ, φ), we have:
| i\j |    0 (θ)        |    1 (φ)        |
|-----|-----------------|-----------------|
|  0  | rotMθθ θ φ      | rotMθφ θ φ      |
|  1  | rotMθφ θ φ      | rotMφφ θ φ      |

All have operator norm ≤ 1.
-/

/-- The operator A[i,j] for second partials of the outer rotation projection. -/
noncomputable def outer_second_partial_A (θ φ : ℝ) (i j : Fin 2) : ℝ³ →L[ℝ] ℝ² :=
  match i, j with
  | 0, 0 => rotMθθ θ φ
  | 0, 1 => rotMθφ θ φ
  | 1, 0 => rotMθφ θ φ
  | 1, 1 => rotMφφ θ φ

open SymbolicRotation in
/-- The hand-written outer second-partial table agrees with the generated symbolic
table entrywise. -/
lemma outer_second_partial_A_eq_symbolic (θ φ : ℝ) (i j : Fin 2) :
    outer_second_partial_A θ φ i j = (secondOuterTerm i j).eval θ φ := by
  fin_cases i <;> fin_cases j <;> rfl

/-- All A[i,j] have operator norm ≤ 1 for outer partials. -/
lemma outer_second_partial_A_norm_le (θ φ : ℝ) (i j : Fin 2) :
    ‖outer_second_partial_A θ φ i j‖ ≤ 1 := by
  rw [outer_second_partial_A_eq_symbolic]
  exact (SymbolicRotation.secondOuterTerm i j).norm_le_one θ φ

/-- The outer second-partial table is symmetric. -/
lemma outer_second_partial_A_symm (θ φ : ℝ) (i j : Fin 2) :
    outer_second_partial_A θ φ i j = outer_second_partial_A θ φ j i := by
  rw [outer_second_partial_A_eq_symbolic, outer_second_partial_A_eq_symbolic,
    SymbolicRotation.secondOuter_comm]

/-!
## Second partials as inner products
-/

open SymbolicRotation in
/-- The second partials of the outer projection are given pointwise by the
`outer_second_partial_A` table. -/
theorem second_partial_rotproj_outer_eq (S : ℝ³) (w : ℝ²) (x : E 2) (i j : Fin 2) :
    nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x =
      ⟪outer_second_partial_A (x.ofLp 0) (x.ofLp 1) i j S, w⟫ := by
  obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (secondOuter_defined i j)
  have hiter := iterPartialOuter_eval_eq [i, j] (t := outerBase) (t' := t') ht S w
  have hA : outer_second_partial_A (x.ofLp 0) (x.ofLp 1) i j =
      t'.eval (x.ofLp 0) (x.ofLp 1) := by
    rw [outer_second_partial_A_eq_symbolic]
    simp only [secondOuterTerm, ht, Option.getD_some]
  rw [show nth_partial i (nth_partial j
      (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) =
        iterPartialOuter [i, j]
          (fun y : E 2 => ⟪(outerBase.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫) from rfl,
    hiter, hA]

/-- Function-level form of `second_partial_rotproj_outer_eq`. -/
theorem nth_partial_nth_partial_rotproj_outer (S : ℝ³) (w : ℝ²) (i j : Fin 2) :
    nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) =
      fun y => ⟪outer_second_partial_A (y.ofLp 0) (y.ofLp 1) i j S, w⟫ :=
  funext fun y => second_partial_rotproj_outer_eq S w y i j

/-!
## Third partials (outer)

Differentiating the `outer_second_partial_A` table once more.  Only 4 distinct
values occur: -rotMθ, rotMθθφ, rotMθφφ, -rotMφ (using Mθθθ = -Mθ, Mφφφ = -Mφ).
-/

/-- The operator A₃[i,j,k] for third partials of the outer rotation projection:
the ∂ᵢ-derivative of `outer_second_partial_A · · j k`. -/
noncomputable def outer_third_partial_A (θ φ : ℝ) (i j k : Fin 2) : ℝ³ →L[ℝ] ℝ² :=
  match i, j, k with
  | 0, 0, 0 => -(rotMθ θ φ)
  | 1, 0, 0 => rotMθθφ θ φ
  | 0, 0, 1 => rotMθθφ θ φ
  | 1, 0, 1 => rotMθφφ θ φ
  | 0, 1, 0 => rotMθθφ θ φ
  | 1, 1, 0 => rotMθφφ θ φ
  | 0, 1, 1 => rotMθφφ θ φ
  | 1, 1, 1 => -(rotMφ θ φ)

open SymbolicRotation in
/-- The hand-written outer third-partial table agrees with the generated symbolic
table entrywise. -/
lemma outer_third_partial_A_eq_symbolic (θ φ : ℝ) (i j k : Fin 2) :
    outer_third_partial_A θ φ i j k = (thirdOuterTerm i j k).eval θ φ := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

/-- All outer A₃[i,j,k] have operator norm ≤ 1. -/
lemma outer_third_partial_A_norm_le (θ φ : ℝ) (i j k : Fin 2) :
    ‖outer_third_partial_A θ φ i j k‖ ≤ 1 := by
  rw [outer_third_partial_A_eq_symbolic]
  exact (SymbolicRotation.thirdOuterTerm i j k).norm_le_one θ φ

/-- The outer third-partial table is symmetric in its first two indices. -/
lemma outer_third_partial_A_swap_first (θ φ : ℝ) (i j k : Fin 2) :
    outer_third_partial_A θ φ i j k = outer_third_partial_A θ φ j i k := by
  rw [outer_third_partial_A_eq_symbolic, outer_third_partial_A_eq_symbolic,
    SymbolicRotation.thirdOuter_swap_first]

/-- The outer third-partial table is symmetric in its last two indices. -/
lemma outer_third_partial_A_swap_last (θ φ : ℝ) (i j k : Fin 2) :
    outer_third_partial_A θ φ i j k = outer_third_partial_A θ φ i k j := by
  rw [outer_third_partial_A_eq_symbolic, outer_third_partial_A_eq_symbolic,
    SymbolicRotation.thirdOuter_swap_last]

open SymbolicRotation in
/-- The third partials of the outer projection are given pointwise by the
`outer_third_partial_A` table. -/
theorem third_partial_rotproj_outer_eq (S : ℝ³) (w : ℝ²) (x : E 2) (i j k : Fin 2) :
    nth_partial i (nth_partial j (nth_partial k
        (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫))) x =
      ⟪outer_third_partial_A (x.ofLp 0) (x.ofLp 1) i j k S, w⟫ := by
  obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (thirdOuter_defined i j k)
  have hiter := iterPartialOuter_eval_eq [i, j, k] (t := outerBase) (t' := t') ht S w
  have hA : outer_third_partial_A (x.ofLp 0) (x.ofLp 1) i j k =
      t'.eval (x.ofLp 0) (x.ofLp 1) := by
    rw [outer_third_partial_A_eq_symbolic]
    simp only [thirdOuterTerm, ht, Option.getD_some]
  rw [show nth_partial i (nth_partial j (nth_partial k
      (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫))) =
        iterPartialOuter [i, j, k]
          (fun y : E 2 => ⟪(outerBase.eval (y.ofLp 0) (y.ofLp 1)) S, w⟫) from rfl,
    hiter, hA]

theorem third_partial_inner_rotM_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (i j k : Fin 2) (y : ℝ²) :
    |nth_partial i (nth_partial j (nth_partial k (rotproj_outer_unit S w))) y| ≤ 1 := by
  have hf_smooth : ContDiff ℝ 3 (fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) :=
    ContDiff.inner ℝ (ContDiff.rotM_outer S) contDiff_const
  have hg_c2 : ContDiff ℝ 2
      (nth_partial k (fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫)) :=
    hf_smooth.fderiv_right (by decide : (2 : WithTop ℕ∞) + 1 ≤ 3) |>.clm_apply contDiff_const
  have hscale : nth_partial i (nth_partial j (nth_partial k (rotproj_outer_unit S w))) y =
      nth_partial i (nth_partial j (nth_partial k
        (fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫))) y / ‖S‖ :=
    nth_partial_nth_partial_nth_partial_div_const i j k _ ‖S‖ y
      (hf_smooth.differentiable (by decide)) (hg_c2.differentiable (by decide))
      ((hg_c2.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
        contDiff_const).differentiable (by decide))
  rw [hscale, third_partial_rotproj_outer_eq S w y i j k]
  exact inner_bound_helper _ S w w_unit (outer_third_partial_A_norm_le _ _ i j k)

theorem rotation_third_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    third_partials_bounded (rotproj_outer_unit S w) := fun x i j k =>
  third_partial_inner_rotM_outer S w_unit i j k x

end GlobalTheorem
