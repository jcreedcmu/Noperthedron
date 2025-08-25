import NegativeRupert.Basic

/--
Parameters that give an orthographic camera view.

TODO: a plain description of what azimuth and elevation mean.
-/
structure ViewParams : Type where
  aziumth : ℝ
  elevation : ℝ

/--
One pose consisting of two views, a spin, and an offset
which is a candidate for evidence that a shape is rupert.
-/
structure ViewPose : Type where
  innerView : ViewParams
  outerView : ViewParams
  innerSpin : ℝ
  innerOffset : ℝ²

/--
A view-format pose together with a shape. This is enough data to
make being "safe" a meaningful property, see MatrixCand.Safe below.
-/
structure ViewCand : Type where
  pose : ViewPose
  shape : Shape

namespace ViewCand

def outerShadow (c : ViewCand) : Set ℝ² :=
  sorry

def innerShadow (c : ViewCand) : Set ℝ² :=
  sorry

/--
A candidate is "safe" if it does not admit a Rupert solution.
-/
def Safe (c : ViewCand) : Prop :=
 sorry

end ViewCand
