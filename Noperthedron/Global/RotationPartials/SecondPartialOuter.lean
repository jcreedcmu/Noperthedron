/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationPartials.RotMOuter
import Noperthedron.Global.Basic

/-!
# Second Partial Outer Lemmas

This file contains:
- `comp_norm_le_one`, `neg_comp_norm_le_one` (private helpers)
- **`second_partial_inner_rotM_outer`** (4 cases: θθ, θφ, φθ, φφ)
- **`rotation_partials_bounded_outer`**
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

/- [SY25] Lemma 19 (outer part) -/
theorem second_partial_inner_rotM_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) (i j : Fin 2) (y : ℝ²) :
    |(fderiv ℝ (fun z => (fderiv ℝ (rotproj_outer_unit S w) z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single j 1)| ≤ 1 := by
  sorry

theorem rotation_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_outer_unit S w) := by
  sorry

end GlobalTheorem
