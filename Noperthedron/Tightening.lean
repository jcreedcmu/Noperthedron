import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic
import Noperthedron.Nopert
import Noperthedron.ViewPose
import Noperthedron.PoseInterval

open Real
namespace Tightening

theorem lemma7_1 (θ φ : ℝ) :
    (rotM (θ + 2/15*π) φ) '' nopert.hull = rotM θ φ '' nopert.hull := by
  ext p
  simp only [Set.mem_image]
  sorry

theorem lemma7_2 (θ φ α : ℝ) :
  (rotR (α + π) ∘L rotM θ φ) '' nopert.hull = (rotR α ∘L rotM θ φ) '' nopert.hull := by
    sorry

theorem lemma7_3 (θ φ : ℝ) :
  (flip_y ∘L rotM θ φ) '' nopert.hull = (-rotM (θ + π / 15) (π - φ)) '' nopert.hull := by
    sorry

-- [SY25] §2.2, Corollary 8
-- This is a piece that relies on symmetry of the Noperthedron
theorem rupert_tightening (p : Pose) (r : Shadows.IsRupert p nopert.hull) :
    ∃ p' : Pose, tightInterval.contains p' ∧ Shadows.IsRupert p' nopert.hull := by
  sorry -- TODO(medium-hard)

end Tightening
