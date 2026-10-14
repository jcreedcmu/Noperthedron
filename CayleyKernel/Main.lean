module

public import CayleyKernel.Gen.All
public import Cayley.Soundness.KMain
public import Noperthedron.MainTheorem
public import Noperthedron.Vertices.InteriorNonempty

@[expose] public section

/-!
# The Noperthedron is not Rupert (kernel-checked, Cayley coordinates)

The certificate is the tree in `CayleyKernel/Gen`: every leaf check is proved by `Eq.refl true`,
so the kernel itself runs the checker. `Cayley.Pack.kernel_sound` turns the per-root facts into
the theorem.
-/

namespace Cayley.KProof

open Cayley.K Cayley.Pack Noperthedron

set_option maxRecDepth 100000 in
theorem noperthedron_not_rupert : ¬ IsRupert exactVerts := by
  apply kernel_sound
  intro i hi
  interval_cases i
  · refine ⟨S_0, _, skel_0, ?_, all_0⟩
    exact holes_0
  · refine ⟨S_1, _, skel_1, ?_, all_1⟩
    exact holes_1
  · refine ⟨S_2, _, skel_2, ?_, all_2⟩
    exact holes_2
  · refine ⟨S_3, _, skel_3, ?_, all_3⟩
    exact holes_3
  · refine ⟨S_4, _, skel_4, ?_, all_4⟩
    exact holes_4
  · refine ⟨S_5, _, skel_5, ?_, all_5⟩
    exact holes_5
  · refine ⟨S_6, _, skel_6, ?_, all_6⟩
    exact holes_6
  · refine ⟨S_7, _, skel_7, ?_, all_7⟩
    exact holes_7
  · refine ⟨S_8, _, skel_8, ?_, all_8⟩
    exact holes_8
  · refine ⟨S_9, _, skel_9, ?_, all_9⟩
    exact holes_9
  · refine ⟨S_10, _, skel_10, ?_, all_10⟩
    exact holes_10
  · refine ⟨S_11, _, skel_11, ?_, all_11⟩
    exact holes_11
  · refine ⟨S_12, _, skel_12, ?_, all_12⟩
    exact holes_12
  · refine ⟨S_13, _, skel_13, ?_, all_13⟩
    exact holes_13
  · refine ⟨S_14, _, skel_14, ?_, all_14⟩
    exact holes_14

/-- There exists a convex polyhedron that does not have the Rupert property. -/
theorem exists_not_rupert : ExistsNonRupertPolyhedron :=
  ⟨exactVerts, interior_exactVerts_hull_nonempty, noperthedron_not_rupert⟩

end Cayley.KProof

end
