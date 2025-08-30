import Rupert.Basic
import NegativeRupert.PoseClasses
import NegativeRupert.Basic
import NegativeRupert.Nopert
import NegativeRupert.ViewPose
import NegativeRupert.TightViewPose

-- [SY25] §2.2, Corollary 8
-- TODO(medium-hard)
-- This is a piece that relies on symmetry of the Noperthedron
theorem rupert_tightening (p : ViewPose) (r : Shadows.IsRupert p nopert.hull) :
    ∃ p' : TightViewPose, Shadows.IsRupert p' nopert.hull := by
  sorry
