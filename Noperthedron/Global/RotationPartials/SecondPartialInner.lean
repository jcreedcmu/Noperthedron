/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.RotationPartials.SecondPartialOuter

/-!
# Second Partial Inner Lemmas

This file contains:
- **`second_partial_inner_rotM_inner`** (9 cases)
- **`rotation_partials_bounded`** (the main theorem from [SY25] Lemma 19)
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

/- [SY25] Lemma 19 (inner part) -/
theorem second_partial_inner_rotM_inner (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) (i j : Fin 3) (y : ℝ³) :
    |(fderiv ℝ (fun z => (fderiv ℝ (rotproj_inner_unit S w) z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single j 1)| ≤ 1 := by
  sorry

/- [SY25] Lemma 19 -/
theorem rotation_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    mixed_partials_bounded (rotproj_inner_unit S w) := by
  sorry

end GlobalTheorem
