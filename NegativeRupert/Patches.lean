import NegativeRupert.Basic
import NegativeRupert.Snub

/--
Given a rotation R in SO(3), we can hit the snub cube with R
and see which vertices are now supporting the convex hull.
We call these the induced vertices of R.

A patch is an equivalence class of rotations in SO(3), where two
rotations are equivalent if they have the same induced vertices.

Some annoying boundary things happen at the boundaries of patches.
We ignore them for now.

We can name a patch by naming the set of induced vertices.
-/
def Patch : Type := Vector Bool snubCubeNumVerts
