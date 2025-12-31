import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet
import Noperthedron.Basic
import Noperthedron.Nopert
import Noperthedron.PoseInterval
import Noperthedron.Tightening
import Noperthedron.ConvertPose
import Noperthedron.CommonCenter
import Noperthedron.ComputationalStep

open scoped Matrix

/--
There is no tight pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_tight_pose : ¬ ∃ v : Pose,
    tightInterval.contains v ∧ RupertPose v nopert.hull := by
  rintro ⟨v, h1, h2⟩
  let ⟨tab, htab, row, hrow, tight⟩ := exists_solution_table
  exact Solution.Row.valid_imp_not_rupert tab htab row hrow ⟨v, tight v h1, h2⟩

/--
There is no pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_pose : ¬ ∃ v : Pose, RupertPose v nopert.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  exact no_nopert_tight_pose (Tightening.rupert_tightening p r)

/--
There is no purely rotational pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_rot_pose : ¬ ∃ p : MatrixPose, RupertPose p.zeroOffset nopert.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  let ⟨v, e⟩ := pose_of_matrix_pose p
  refine no_nopert_pose ⟨v, ?_⟩
  apply (converted_pose_rupert_iff v nopert.hull).mpr
  rw [e]
  exact r

/--
There is no pose that makes the Noperthedron have the Rupert property
-/
theorem no_nopert_matrix_pose : ¬ ∃ p : MatrixPose, RupertPose p nopert.hull := by
  intro r
  obtain ⟨p, r⟩ := r
  have hconvex : Convex ℝ nopert.hull := by
    unfold Shape.hull
    exact convex_convexHull ℝ (↑nopert.vertices : Set ℝ³)
  have r' := rupert_implies_rot_rupert nopert_point_symmetric hconvex p r
  exact no_nopert_rot_pose ⟨p, r'⟩

/--
If a set is Rupert according to the standard definition, then we can
package up the pose parameters. The converse also should be true, but
there hasn't been any need for it yet.
-/
lemma rupert_set_implies_pose_rupert {S : Set ℝ³} (r : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, inner_so3, offset, outer, outer_so3, sub⟩ := r
  let p : MatrixPose := MatrixPose.mk ⟨inner, inner_so3⟩ ⟨outer, outer_so3⟩ offset
  use p
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  rw [p.inner_shadow_lemma, outerShadow]
  repeat rw [← proj_xy_eq_proj_xyL]
  exact sub

/--
The Noperthedron (as a subset of ℝ³) is not Rupert
-/
theorem nopert_not_rupert_set : ¬ IsRupertSet nopert.hull := fun r =>
  no_nopert_matrix_pose (rupert_set_implies_pose_rupert r)

/--
FIXME: `sortedVerts` and the lemma `mem_iff_symm_mem` are a temporary
hack so I can proceed with a refactoring piecemeal. We'd rather work
with `Finset ℝ³` in as many places as possible, and this is the
conversion from that to picking a specific finite type ι and a map ι →
ℝ³.
-/
noncomputable
def sortedVerts : Fin nopert.vertices.card → ℝ³ := fun i => nopertVerts.equivFin.symm i

lemma mem_iff_symm_mem {a : Type} {A : Finset a} {n : ℕ} {x : a} (eq : ↥A ≃ Fin n) :
    x ∈ A ↔ ∃ y, eq.symm y = x := by
  constructor
  · intro hx
    use eq ⟨x, hx⟩
    simp only [Equiv.symm_apply_apply]
  · rintro ⟨y, hy⟩
    rw [← hy]
    simp

/--
The Noperthedron is not Rupert.

FIXME: Ideally we'd like to reconcile this with
[https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/Rupert.lean](the
formal-conjectures formulation) which will require some minor
impedance matching, and an extra proof obligation that the interior of
the Noperthedron is nonempty.
-/
theorem nopert_not_rupert : ¬ IsRupert sortedVerts := by
  intro r

  refine nopert_not_rupert_set ?_
  unfold Shape.hull

  have hsort : ↑nopert.vertices = Set.range sortedVerts := by
    ext v
    simp [sortedVerts]
    exact mem_iff_symm_mem nopertVerts.equivFin

  rw [hsort]
  exact rupert_iff_rupert_set sortedVerts |>.mp r
