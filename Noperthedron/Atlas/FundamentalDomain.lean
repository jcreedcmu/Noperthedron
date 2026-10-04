module

public import Mathlib.Data.Finset.Max
public import Noperthedron.Cayley
public import Noperthedron.Atlas.Tightening

@[expose] public section


/-!
# Relative rotations

The relative rotation of a matrix pose lies in SO(3).

(Generic; contains only what the Nopert #231 proof uses.)
-/

namespace Noperthedron.Atlas

open scoped Matrix

/-- Relative rotation of a full pose, with the outer frame pulled back. -/
def _root_.MatrixPose.relativeRotation (p : MatrixPose) :
    Matrix (Fin 3) (Fin 3) ℝ := p.outerRot.valᵀ * p.innerRot.val

theorem MatrixPose.relativeRotation_mem_SO3 (p : MatrixPose) :
    p.relativeRotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hout := (Matrix.mem_specialOrthogonalGroup_iff).mp p.outerRot.property
  have houtT : p.outerRot.valᵀ ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_iff,
      Matrix.mem_orthogonalGroup_iff]
    constructor
    · simpa only [Matrix.transpose_transpose] using
        (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hout.1
    · simpa only [Matrix.det_transpose] using hout.2
  exact Submonoid.mul_mem _ houtT p.innerRot.property

end Noperthedron.Atlas

end
