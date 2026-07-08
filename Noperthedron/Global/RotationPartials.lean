/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Noperthedron.Global.RotationPartials.Rotproj
import Noperthedron.Global.RotationPartials.RotMOuter
import Noperthedron.Global.RotationPartials.SecondPartialOuter
import Noperthedron.Global.RotationPartials.SecondPartialInner

/-!
# Rotation Partial Derivatives

This module aggregates all the rotation partial derivative lemmas:
- `Rotproj.lean`: HasFDerivAt.rotproj_inner and supporting lemmas
- `RotMOuter.lean`: HasFDerivAt.rotM_outer and related lemmas
- `SecondPartialOuter.lean`: third_partial_inner_rotM_outer, rotation_third_partials_bounded_outer
- `SecondPartialInner.lean`: third_partial_inner_rotM_inner, rotation_third_partials_bounded
-/
