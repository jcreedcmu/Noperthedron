module

public import Noperthedron.Nopert231.AtlasProjectiveLocalCertificate
public import Noperthedron.Nopert231.AtlasProjectiveAnnularCertificate

@[expose] public section

/-!
# Shared projective-view atlas for symmetry-local rigidity

The expensive balanced-support geometry depends on the outer view but not on
the Cayley interval or chart.  This tree checks that geometry once.  A small
`Tube` then supplies only the chart-dependent mismatch bound, allowing every
near-symmetry leaf in the main search to reuse the same view atlas.
-/

namespace Noperthedron.Nopert231.AtlasProjectiveLocalViewTree

variable {P : C5Model}

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

structure Tube where
  interval : AtlasInterval ℚ
  chart : CayleyAtlas.ChartIndex
  symmetryIndex : OrbitIndex
  r : ℚ
deriving DecidableEq

def Tube.shell (tube : Tube) : AtlasLocalCertificate.Box where
  interval := tube.interval
  chart := tube.chart
  symmetryIndex := tube.symmetryIndex
  certificate := fun _ => { contact := fun _ => { index := 0, direction := 0 } }
  c := 0
  r := tube.r

abbrev Tube.mismatchRadius (tube : Tube) : ℚ := tube.shell.mismatchRadius

def Tube.Valid (tube : Tube) : Prop := tube.mismatchRadius ≤ tube.r

instance (tube : Tube) : Decidable tube.Valid := by
  unfold Tube.Valid
  infer_instance

inductive Row where
  /-- An interior node. `rLower` is a certified lower bound on the tube
  radius of every certificate in its subtree (each child's `rLower` is at
  least it), so a tube of radius `≤ rLower` is ruled out on the node's
  triangle even when other parts of the table only certify a smaller tube. -/
  | split (id : ℕ) (children : Fin 4 → ℕ)
      (root : Fin 8) (triangle : AtlasProjectiveView.Triangle ℚ) (rLower : ℚ)
  | certificate (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
  | decomposed (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
      (coreAxis : AxisCertificate)
      (defect0 : Fin 3 → ℚ) (D0 : ℚ)
      (r_min c_cone c_core lam : ℚ)
      (w : Fin 3 → ℚ)
  | flockDecomposed (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
      (flockAxes : Array AxisCertificate)
      (defect0 : Fin 3 → ℚ) (D0 : ℚ)
      (r_min c_cone c_core S_max T_max : ℚ)
      (tree : QuadCoverTree)
deriving DecidableEq

def Row.id : Row → ℕ
  | .split id .. | .certificate id .. | .decomposed id .. | .flockDecomposed id .. => id

def Row.root : Row → Fin 8
  | .split _ _ root _ _ | .certificate _ { root, .. } | .decomposed _ { root, .. } .. | .flockDecomposed _ { root, .. } .. => root

def Row.triangle : Row → AtlasProjectiveView.Triangle ℚ
  | .split _ _ _ triangle _ | .certificate _ { triangle, .. } | .decomposed _ { triangle, .. } .. | .flockDecomposed _ { triangle, .. } .. => triangle

/-- The certified tube radius lower bound of a node: stored on interior nodes,
the certificate's own radius on leaves. -/
def Row.rLower : Row → ℚ
  | .split _ _ _ _ rLower => rLower
  | .certificate _ box | .decomposed _ box .. | .flockDecomposed _ box .. => box.r

instance : Inhabited Row where
  default := .split 0 (fun _ => 0) 0 upperWedgeTriangle 0

def Row.ValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Row → Prop
  | .split id children root triangle rLower => r ≤ rLower ∧ ∀ child,
      id < children child ∧ children child < size ∧
      (get (children child)).root = root ∧
      (get (children child)).triangle =
        Noperthedron.SnubCube.ProjectiveView.split triangle child ∧
      rLower ≤ (get (children child)).rLower
  | .certificate _ box =>
      box.symmetryIndex = symmetryIndex ∧ r ≤ box.r ∧ box.ViewValid
  | .decomposed _ box coreAxis defect0 D0 r_min c_cone c_core lam w =>
      box.symmetryIndex = symmetryIndex ∧ r ≤ box.r ∧
      box.DecomposedViewValid coreAxis defect0 D0 r_min c_cone c_core lam w
  | .flockDecomposed _ box flockAxes defect0 D0 r_min c_cone c_core S_max T_max tree =>
      box.symmetryIndex = symmetryIndex ∧ r ≤ box.r ∧
      box.FlockDecomposedViewValid flockAxes defect0 D0 r_min c_cone c_core S_max T_max tree

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) (row : Row) :
    Decidable (row.ValidAt symmetryIndex r get size) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Prop :=
  ∀ i : Fin size,
    (get i).id = i ∧ (get i).ValidAt symmetryIndex r get size

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) : Decidable (RowsValidAt symmetryIndex r get size) := by
  unfold RowsValidAt
  infer_instance

/-- A kernel-checkable slice of `RowsValidAt`.  Generated local-view tables
prove small slices independently and join them, so kernel reduction never has
to unfold the entire certificate atlas at once. -/
def RowsValidRangeAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size start count : ℕ) : Prop :=
  start + count ≤ size ∧ ∀ j : Fin count,
    (get (start + j.val)).id = start + j.val ∧
      (get (start + j.val)).ValidAt symmetryIndex r get size

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size start count : ℕ) :
    Decidable (RowsValidRangeAt symmetryIndex r get size start count) := by
  unfold RowsValidRangeAt
  infer_instance

theorem rowsValidRange_append {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size start left right : ℕ}
    (hleft : RowsValidRangeAt symmetryIndex r get size start left)
    (hright : RowsValidRangeAt symmetryIndex r get size (start + left) right) :
    RowsValidRangeAt symmetryIndex r get size start (left + right) := by
  unfold RowsValidRangeAt at hleft hright ⊢
  constructor
  · omega
  · intro j
    by_cases hmid : j.val < left
    · simpa using hleft.2 ⟨j.val, hmid⟩
    · have hjright : j.val - left < right := by omega
      have hr := hright.2 ⟨j.val - left, hjright⟩
      have hi : start + left + (j.val - left) = start + j.val := by omega
      simpa [hi] using hr

theorem rowsValidAt_of_range {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size : ℕ}
    (h : RowsValidRangeAt symmetryIndex r get size 0 size) :
    RowsValidAt symmetryIndex r get size := by
  intro i
  simpa using h.2 ⟨i.val, i.isLt⟩

theorem valid_imp_not_rupert_ix (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt symmetryIndex r get size)
    (i : ℕ) (hi : i < size) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = symmetryIndex)
    (htubeRadius : tube.r ≤ (get i).rLower) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale (get i).root p)
    (hmem : InTriangle (toReal (get i).triangle)
      (normalizedView (get i).root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      P.polyhedron.hull := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid hscale hmem htubeRadius ⊢
  cases row with
  | split id children root triangle rLower =>
      obtain ⟨child, hchildMem⟩ := mem_split hmem
      obtain ⟨hforward, hchildSize, hchildRoot, hchildTriangle, hchildRadius⟩ :=
        hvalid.2 child
      have hchild := valid_imp_not_rupert_ix symmetryIndex r get size
        rowsValid (children child) hchildSize tube htubeSymmetry
        (le_trans htubeRadius hchildRadius) htube hp offset
      rw [hchildRoot, hchildTriangle] at hchild
      exact hchild hscale hchildMem
  | certificate id box =>
      obtain ⟨hboxSymmetry, hboxRadius, hview⟩ := hvalid
      let actual := box.retarget tube.interval tube.chart
      have hactualView : actual.ViewValid :=
        hview.retarget tube.interval tube.chart
      have hmismatch : actual.mismatchRadius ≤ actual.r := by
        have hsym : box.symmetryIndex = tube.symmetryIndex :=
          hboxSymmetry.trans htubeSymmetry.symm
        have hmismatchTube : actual.mismatchRadius ≤ tube.r := by
          simpa [actual, Box.retarget, Box.mismatchRadius,
            Box.mismatchShell, Tube.Valid, Tube.mismatchRadius, Tube.shell,
            AtlasLocalCertificate.Box.mismatchRadius,
            AtlasLocalCertificate.Box.identityMismatchRadius,
            AtlasLocalCertificate.Box.identityRadiusSqUpper,
            AtlasLocalCertificate.Box.coordinateAbsUpper,
            AtlasLocalCertificate.Box.mismatchFrobeniusSqUpper,
            AtlasLocalCertificate.Box.entryAbsUpper,
            AtlasLocalCertificate.Box.mismatchBall,
            AtlasLocalCertificate.Box.variableBalls,
            AtlasLocalCertificate.Box.mismatchQuadratic,
            hsym]
            using htube
        have hr : tube.r ≤ box.r := htubeRadius
        simpa [actual, Box.retarget] using hmismatchTube.trans hr
      have hactual : actual.Valid :=
        Box.Valid.of_viewValid hactualView hmismatch
      exact actual.valid_imp_not_translated_rupert hactual hp offset
        hscale hmem
  | decomposed id box coreAxis defect0 D0 r_min c_cone c_core lam w =>
      obtain ⟨hboxSymmetry, hboxRadius, hview⟩ := hvalid
      let actual := box.retarget tube.interval tube.chart
      have hactualView : actual.DecomposedViewValid coreAxis defect0 D0 r_min c_cone c_core lam w :=
        hview.retarget tube.interval tube.chart
      have hmismatch : actual.mismatchRadius ≤ actual.r := by
        have hsym : box.symmetryIndex = tube.symmetryIndex :=
          hboxSymmetry.trans htubeSymmetry.symm
        have hmismatchTube : actual.mismatchRadius ≤ tube.r := by
          simpa [actual, Box.retarget, Box.mismatchRadius,
            Box.mismatchShell, Tube.Valid, Tube.mismatchRadius, Tube.shell,
            AtlasLocalCertificate.Box.mismatchRadius,
            AtlasLocalCertificate.Box.identityMismatchRadius,
            AtlasLocalCertificate.Box.identityRadiusSqUpper,
            AtlasLocalCertificate.Box.coordinateAbsUpper,
            AtlasLocalCertificate.Box.mismatchFrobeniusSqUpper,
            AtlasLocalCertificate.Box.entryAbsUpper,
            AtlasLocalCertificate.Box.mismatchBall,
            AtlasLocalCertificate.Box.variableBalls,
            AtlasLocalCertificate.Box.mismatchQuadratic,
            hsym]
            using htube
        have hr : tube.r ≤ box.r := htubeRadius
        simpa [actual, Box.retarget] using hmismatchTube.trans hr
      exact actual.valid_imp_not_translated_rupert_of_decomposedViewValid
        coreAxis defect0 D0 r_min c_cone c_core lam w
        hactualView hmismatch hp offset hscale hmem
  | flockDecomposed id box flockAxes defect0 D0 r_min c_cone c_core S_max T_max tree =>
      obtain ⟨hboxSymmetry, hboxRadius, hview⟩ := hvalid
      let actual := box.retarget tube.interval tube.chart
      have hactualView : actual.FlockDecomposedViewValid flockAxes defect0 D0 r_min c_cone c_core S_max T_max tree :=
        hview.retarget tube.interval tube.chart
      have hmismatch : actual.mismatchRadius ≤ actual.r := by
        have hsym : box.symmetryIndex = tube.symmetryIndex :=
          hboxSymmetry.trans htubeSymmetry.symm
        have hmismatchTube : actual.mismatchRadius ≤ tube.r := by
          simpa [actual, Box.retarget, Box.mismatchRadius,
            Box.mismatchShell, Tube.Valid, Tube.mismatchRadius, Tube.shell,
            AtlasLocalCertificate.Box.mismatchRadius,
            AtlasLocalCertificate.Box.identityMismatchRadius,
            AtlasLocalCertificate.Box.identityRadiusSqUpper,
            AtlasLocalCertificate.Box.coordinateAbsUpper,
            AtlasLocalCertificate.Box.mismatchFrobeniusSqUpper,
            AtlasLocalCertificate.Box.entryAbsUpper,
            AtlasLocalCertificate.Box.mismatchBall,
            AtlasLocalCertificate.Box.variableBalls,
            AtlasLocalCertificate.Box.mismatchQuadratic,
            hsym]
            using htube
        have hr : tube.r ≤ box.r := htubeRadius
        simpa [actual, Box.retarget] using hmismatchTube.trans hr
      exact actual.valid_imp_not_translated_rupert_of_flockDecomposedViewValid
        flockAxes defect0 D0 r_min c_cone c_core S_max T_max tree
        hactualView hmismatch hp offset hscale hmem
termination_by size - i
decreasing_by
  all_goals
    have : id = i := by simpa [Row.id, hrow] using hid
    omega

/-- Every node's radius bound is at least the table-wide radius `r`. -/
theorem le_rLower_of_rowsValid {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size : ℕ}
    (rowsValid : RowsValidAt symmetryIndex r get size) (i : ℕ) (hi : i < size) :
    r ≤ (get i).rLower := by
  obtain ⟨-, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize get i = row at hvalid ⊢
  cases row <;> first | exact hvalid.1 | exact hvalid.2.1

structure Table where
  symmetryIndex : OrbitIndex
  r : ℚ
  root : Fin 8 := 0
  triangle : AtlasProjectiveView.Triangle ℚ := upperWedgeTriangle
  get : ℕ → Row
  size : ℕ

def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.symmetryIndex table.r table.get table.size ∧
    (table.get 0).root = table.root ∧
    (table.get 0).triangle = table.triangle

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

/-- Walk the quaternary quadtree starting from root (row 0), following the
subdivision path. -/
def Table.findNode (table : Table) (path : List (Fin 4)) : Option ℕ :=
  let rec loop (currId : ℕ) : List (Fin 4) → Option ℕ
    | [] => if currId < table.size then some currId else none
    | c :: cs =>
        if currId < table.size then
          match table.get currId with
          | .certificate .. | .decomposed .. | .flockDecomposed .. => none
          | .split _ children .. => loop (children c) cs
        else
          none
  loop 0 path

/-- A valid table rules out every tube up to the radius bound of the node
whose triangle contains the view. -/
theorem Table.valid_imp_not_translated_rupert_at_node_rLower (table : Table)
    (hvalid : table.Valid) (nodeId : ℕ) (hnode : nodeId < table.size) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r ≤ (table.get nodeId).rLower) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale (table.get nodeId).root p)
    (hmem : InTriangle (toReal (table.get nodeId).triangle)
      (normalizedView (table.get nodeId).root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      P.polyhedron.hull := by
  obtain ⟨hnonempty, hrows, -, -⟩ := hvalid
  exact valid_imp_not_rupert_ix table.symmetryIndex table.r
    table.get table.size hrows nodeId hnode tube htubeSymmetry htubeRadius
    htube hp offset hscale hmem

theorem Table.valid_imp_not_translated_rupert_at_node (table : Table)
    (hvalid : table.Valid) (nodeId : ℕ) (hnode : nodeId < table.size) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r ≤ table.r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale (table.get nodeId).root p)
    (hmem : InTriangle (toReal (table.get nodeId).triangle)
      (normalizedView (table.get nodeId).root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      P.polyhedron.hull :=
  table.valid_imp_not_translated_rupert_at_node_rLower hvalid nodeId hnode tube
    htubeSymmetry (htubeRadius.trans (le_rLower_of_rowsValid hvalid.2.1 nodeId hnode))
    htube hp offset hscale hmem

theorem Table.valid_imp_not_translated_rupert_in_triangle (table : Table)
    (hvalid : table.Valid) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r ≤ table.r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal)
    (hscale : 1 ≤ viewScale table.root p)
    (hmem : InTriangle (toReal table.triangle)
      (normalizedView table.root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      P.polyhedron.hull := by
  have hchecked := Table.valid_imp_not_translated_rupert_at_node (P := P) table
    hvalid 0 hvalid.1 tube htubeSymmetry htubeRadius htube hp offset
  rw [hvalid.2.2.1, hvalid.2.2.2] at hchecked
  exact hchecked hscale hmem

theorem Table.valid_imp_not_translated_rupert (table : Table)
    (hvalid : table.Valid) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r ≤ table.r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal)
    (hview : p.InViewWedge) (hupper : p.InUpperView) (offset : ℝ²)
    (hroot : table.root = 0) (htriangle : table.triangle = upperWedgeTriangle) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      P.polyhedron.hull := by
  obtain ⟨hscale, hmem⟩ := upperView_mem_wedgeTriangle p hview hupper
  apply table.valid_imp_not_translated_rupert_in_triangle hvalid tube
    htubeSymmetry htubeRadius htube hp
  · simpa [hroot] using hscale
  · simpa [hroot, htriangle] using hmem

/-! ### Views below a node

The 5D search subdivides each code triangle with the same four-way split as
the identity-tube tables, so a 5D view triangle is a node triangle of a table
split further by some digits. -/

/-- `triangle` split successively along `path`. -/
def splitPath (triangle : AtlasProjectiveView.Triangle ℚ) :
    List (Fin 4) → AtlasProjectiveView.Triangle ℚ
  | [] => triangle
  | c :: cs => splitPath (Noperthedron.SnubCube.ProjectiveView.split triangle c) cs

/-- A sub-triangle of the four-way split lies inside its parent. -/
theorem inTriangle_of_split {triangle : AtlasProjectiveView.Triangle ℚ} {child : Fin 4}
    {point : Fin 3 → ℝ}
    (h : InTriangle (toReal (Noperthedron.SnubCube.ProjectiveView.split triangle child)) point) :
    InTriangle (toReal triangle) point := by
  obtain ⟨w, hnonneg, hsum, hpoint⟩ := h
  have h0 := hnonneg 0
  have h1 := hnonneg 1
  have h2 := hnonneg 2
  simp only [Fin.sum_univ_three] at hsum
  fin_cases child
  · refine ⟨![w 0 + w 1 / 2 + w 2 / 2, w 1 / 2, w 2 / 2], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp <;> positivity
    · simp [Fin.sum_univ_three]; linarith
    · rw [hpoint]; funext c
      simp [affinePoint, Fin.sum_univ_three, Noperthedron.SnubCube.ProjectiveView.split, toReal]
      ring
  · refine ⟨![w 0 / 2, w 0 / 2 + w 1 + w 2 / 2, w 2 / 2], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp <;> positivity
    · simp [Fin.sum_univ_three]; linarith
    · rw [hpoint]; funext c
      simp [affinePoint, Fin.sum_univ_three, Noperthedron.SnubCube.ProjectiveView.split, toReal]
      ring
  · refine ⟨![w 0 / 2, w 1 / 2, w 0 / 2 + w 1 / 2 + w 2], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp <;> positivity
    · simp [Fin.sum_univ_three]; linarith
    · rw [hpoint]; funext c
      simp [affinePoint, Fin.sum_univ_three, Noperthedron.SnubCube.ProjectiveView.split, toReal]
      ring
  · refine ⟨![w 0 / 2 + w 2 / 2, w 0 / 2 + w 1 / 2, w 1 / 2 + w 2 / 2], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp <;> positivity
    · simp [Fin.sum_univ_three]; linarith
    · rw [hpoint]; funext c
      simp [affinePoint, Fin.sum_univ_three, Noperthedron.SnubCube.ProjectiveView.split, toReal]
      ring

theorem inTriangle_of_splitPath {triangle : AtlasProjectiveView.Triangle ℚ}
    {path : List (Fin 4)} {point : Fin 3 → ℝ}
    (h : InTriangle (toReal (splitPath triangle path)) point) :
    InTriangle (toReal triangle) point := by
  induction path generalizing triangle with
  | nil => exact h
  | cons c cs ih => exact inTriangle_of_split (ih h)

/-- Walk `path` from the root as far as the table goes. Returns the node
reached and the digits left over (nonempty only when the walk stops at a
leaf). Soundness does not depend on how the node is found, only on its index
being in range. -/
def Table.findNodePrefix (table : Table) (path : List (Fin 4)) :
    Option (ℕ × List (Fin 4)) :=
  let rec loop (currId : ℕ) : List (Fin 4) → Option (ℕ × List (Fin 4))
    | [] => if currId < table.size then some (currId, []) else none
    | c :: cs =>
        if currId < table.size then
          match table.get currId with
          | .split _ children .. => loop (children c) cs
          | _ => some (currId, c :: cs)
        else
          none
  loop 0 path

/-- A valid table rules out tubes up to a node's radius bound on every
sub-triangle of the node's triangle. -/
theorem Table.valid_imp_not_translated_rupert_below_node (table : Table)
    (hvalid : table.Valid) (nodeId : ℕ) (hnode : nodeId < table.size)
    (rest : List (Fin 4)) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r ≤ (table.get nodeId).rLower) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale (table.get nodeId).root p)
    (hmem : InTriangle (toReal (splitPath (table.get nodeId).triangle rest))
      (normalizedView (table.get nodeId).root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      P.polyhedron.hull :=
  table.valid_imp_not_translated_rupert_at_node_rLower hvalid nodeId hnode tube
    htubeSymmetry htubeRadius htube hp offset hscale (inTriangle_of_splitPath hmem)

end Noperthedron.Nopert231.AtlasProjectiveLocalViewTree

end
