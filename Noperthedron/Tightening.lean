import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic
import Noperthedron.Nopert
import Noperthedron.ViewPose
import Noperthedron.PoseInterval

-- [SY25] §2.2, Corollary 8
-- This is a piece that relies on symmetry of the Noperthedron
theorem rupert_tightening (p : ViewPose) (r : Shadows.IsRupert p nopert.hull) :
    ∃ p' : ViewPose, tightInterval.contains p' ∧ Shadows.IsRupert p' nopert.hull := by
  sorry -- TODO(medium-hard)
