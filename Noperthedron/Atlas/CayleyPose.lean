module

public import Noperthedron.Atlas.FundamentalDomain

@[expose] public section


/-!
# Outer rotation and relative rotation

The outer rotation of a pose composed with the relative rotation gives the
inner rotation.

(Extracted, with only what the certificates use, from the earlier snub-cube
proof attempt.)
-/

namespace Noperthedron.Atlas

open scoped Matrix

namespace CayleyPose

end CayleyPose

/-- The inner rotation of any matrix pose is its outer rotation followed by
its relative rotation. -/
theorem MatrixPose.outer_mul_relativeRotation (p : MatrixPose) :
    p.outerRot.val * p.relativeRotation = p.innerRot.val := by
  have horth := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp
    p.outerRot.property.1
  simp only [MatrixPose.relativeRotation, ← Matrix.mul_assoc, horth,
    Matrix.one_mul]

end Noperthedron.Atlas

end
