import Rupert.Basic

def snubCubeNumVerts : ℕ := 24
def snubCubeVerts : Fin snubCubeNumVerts → ℝ³ := sorry

theorem snub_cube_not_rupert : ¬ IsRupert snubCubeVerts := by
 unfold IsRupert
 push_neg
 intros innerRot inner_rot_so3 innerOffset outerRot outer_rot_so3
 lift_lets
 intros hull inner_shadow outer_shadow
 sorry
