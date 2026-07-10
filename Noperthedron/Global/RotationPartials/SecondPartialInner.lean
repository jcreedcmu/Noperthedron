/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationPartials.SecondPartialOuter
import Noperthedron.Global.RotationPartials.Rotproj

/-!
# Second Partial Inner Lemmas

This file contains:
- **`second_partial_rotproj_inner_eq`**, **`third_partial_rotproj_inner_eq`**: the
  second and third partials of `rotproj_inner` equal the `inner_second_partial_A` /
  `inner_third_partial_A` tables. Both are uniform instances of the symbolic bridge
  (`SymbolicRotation.iterPartial_eval_eq`): the derivation is performed symbolically,
  and the hand-written tables agree with the generated ones by
  `inner_second_partial_A_eq_symbolic` / `inner_third_partial_A_eq_symbolic`.
- **`third_partial_inner_rotM_inner`**
- **`rotation_third_partials_bounded`** (the main theorem from [SY25] Lemma 19)
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

open SymbolicRotation in
/-- The second partials of `rotproj_inner` are given pointwise by the
`inner_second_partial_A` table. -/
theorem second_partial_rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j : Fin 3) :
    nth_partial i (nth_partial j (rotproj_inner S w)) x =
      ⟪inner_second_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j S, w⟫ := by
  obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (second_defined i j)
  have hiter := iterPartial_eval_eq [i, j] (t := baseTerm) (t' := t') ht S w
  have hA : inner_second_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j =
      t'.eval (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) := by
    rw [inner_second_partial_A_eq_symbolic]
    simp only [secondTerm, ht, Option.getD_some]
  rw [rotproj_inner_eq_baseTerm,
    show nth_partial i (nth_partial j
      (fun y : E 3 => ⟪(baseTerm.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫)) =
        iterPartial [i, j]
          (fun y : E 3 => ⟪(baseTerm.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫) from rfl,
    hiter, hA]

/-- Function-level form of `second_partial_rotproj_inner_eq`. -/
theorem nth_partial_nth_partial_rotproj_inner (S : ℝ³) (w : ℝ²) (i j : Fin 3) :
    nth_partial i (nth_partial j (rotproj_inner S w)) =
      fun y => ⟪inner_second_partial_A (y.ofLp 0) (y.ofLp 1) (y.ofLp 2) i j S, w⟫ :=
  funext fun y => second_partial_rotproj_inner_eq S w y i j

open SymbolicRotation in
/-- The third partials of `rotproj_inner` are given pointwise by the
`inner_third_partial_A` table. -/
theorem third_partial_rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j k : Fin 3) :
    nth_partial i (nth_partial j (nth_partial k (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j k S, w⟫ := by
  obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (third_defined i j k)
  have hiter := iterPartial_eval_eq [i, j, k] (t := baseTerm) (t' := t') ht S w
  have hA : inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j k =
      t'.eval (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) := by
    rw [inner_third_partial_A_eq_symbolic]
    simp only [thirdTerm, ht, Option.getD_some]
  rw [rotproj_inner_eq_baseTerm,
    show nth_partial i (nth_partial j (nth_partial k
      (fun y : E 3 => ⟪(baseTerm.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫))) =
        iterPartial [i, j, k]
          (fun y : E 3 => ⟪(baseTerm.eval (y.ofLp 0) (y.ofLp 1) (y.ofLp 2)) S, w⟫) from rfl,
    hiter, hA]

/- [SY25] Lemma 19 (inner part) -/
theorem third_partial_inner_rotM_inner (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (i j k : Fin 3) (y : ℝ³) :
    |nth_partial i (nth_partial j (nth_partial k (rotproj_inner_unit S w))) y| ≤ 1 := by
  have hf_smooth : ContDiff ℝ 3 (rotproj_inner S w) := ContDiff.rotproj_inner S w
  have hg_c2 : ContDiff ℝ 2 (nth_partial k (rotproj_inner S w)) :=
    hf_smooth.fderiv_right (by decide : (2 : WithTop ℕ∞) + 1 ≤ 3) |>.clm_apply contDiff_const
  have hg_diff : Differentiable ℝ (nth_partial k (rotproj_inner S w)) :=
    hg_c2.differentiable (by decide)
  have hgg_diff : Differentiable ℝ (nth_partial j (nth_partial k (rotproj_inner S w))) :=
    (hg_c2.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.clm_apply
      contDiff_const).differentiable (by decide)
  have hscale : nth_partial i (nth_partial j (nth_partial k (rotproj_inner_unit S w))) y =
      nth_partial i (nth_partial j (nth_partial k (rotproj_inner S w))) y / ‖S‖ :=
    nth_partial_nth_partial_nth_partial_div_const i j k (rotproj_inner S w) ‖S‖ y
      (Differentiable.rotproj_inner S w) hg_diff hgg_diff
  rw [hscale, third_partial_rotproj_inner_eq S w y i j k]
  exact inner_bound_helper _ S w w_unit (inner_third_partial_A_norm_le _ _ _ i j k)

/- [SY25] Lemma 19 -/
theorem rotation_third_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    third_partials_bounded (rotproj_inner_unit S w) := fun x i j k =>
  third_partial_inner_rotM_inner S w_unit i j k x

end GlobalTheorem
