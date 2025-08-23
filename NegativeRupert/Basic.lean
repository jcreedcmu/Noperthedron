import Rupert.Basic

open scoped Matrix

def snubCubeNumVerts : ℕ := 24
def snubCubeVerts : Fin snubCubeNumVerts → ℝ³ := sorry

/--
One configuration consisting of two rotations and an offset
which is a candidate for evidence that a shape is rupert.
-/
structure MatrixConfig : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

/--
A finite collection of vertices in ℝ³
-/
structure Shape : Type where
  size : ℕ
  vertices : Fin size → ℝ³

/--
A matrix config together with a shape. This is a standalone candidate
for being "safe", see MatrixWitness.Safe below.
-/
structure MatrixWitness : Type where
  config : MatrixConfig
  shape : Shape

namespace MatrixWitness

def hull (w : MatrixWitness) : Set ℝ³ := convexHull ℝ { w.shape.vertices i | i }

def innerOffset (w : MatrixWitness) : ℝ² :=
  w.config.innerOffset

def outerShadow (w : MatrixWitness) : Set ℝ² :=
  { proj_xy (w.config.outerRot *ᵥ p) | p ∈ w.hull }

def innerShadow (w : MatrixWitness) : Set ℝ² :=
  { w.innerOffset + proj_xy (w.config.innerRot *ᵥ p) | p ∈ w.hull }

def Safe (w : MatrixWitness) : Prop :=
 ∃ y, y ∈ w.innerShadow ∧ ¬ y ∈ w.outerShadow

end MatrixWitness

/--
Parameters that give an orthographic camera view. The camera is positioned at
(0,-1,0) by default, looking at the origin with (0,0,1) being "up"
and (1,0,0) being "right".

Elevation specifies a rotation of the camera about the x axis, which is applied first.
Azimuth specifies a rotation of the camera about the z axis, which is applied next.
-/
structure ViewParams : Type where
  aziumth : ℝ
  elevation : ℝ

/--
One configuration consisting of two views, a spin, and an offset
which is a candidate for evidence that a shape is rupert.
-/
structure ViewConfig : Type where
  innerView : ViewParams
  outerView : ViewParams
  innerSpin : ℝ
  innerOffset : ℝ²

def matrix_of_view (vc : ViewConfig) : MatrixConfig :=
  let { innerView, outerView, innerSpin, innerOffset } := vc
  { innerRot := sorry,
    outerRot := sorry,
    innerOffset }



def snubCube : Shape := sorry

def snubWitness (mc : MatrixConfig) : MatrixWitness :=
  { config := mc
    shape := snubCube }

theorem all_snub_witnesses_safe : ∀ mc : MatrixConfig, (snubWitness mc).Safe := by
 sorry

theorem snub_cube_not_rupert : ¬ IsRupert snubCube.vertices := by
  unfold IsRupert
  push_neg
  intros innerRot inner_rot_so3 innerOffset outerRot outer_rot_so3
  lift_lets
  intros hull inner_shadow outer_shadow
  refine Set.not_subset.mpr ?_
  let mc : MatrixConfig := {
    innerRot := ⟨innerRot, inner_rot_so3⟩,
    outerRot := ⟨outerRot, outer_rot_so3⟩,
    innerOffset,
  }
  obtain ⟨y, hy, hy'⟩ := all_snub_witnesses_safe mc
  use y
  exact ⟨hy, fun hy2 ↦ hy' (interior_subset hy2)⟩
