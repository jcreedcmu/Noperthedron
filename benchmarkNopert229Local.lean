import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.SparseLocalViewTree

/-! Native timing and validity audit for packed Nopert #229 local rows. -/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.SparseLocalViewTree
open Noperthedron.Nopert229.SparseSupport
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

private def certificateIndices (table : Table) : List Nat :=
  (List.range table.size).filter fun i => match table.get i with
    | .certificate .. => true
    | .split .. => false

private def sampleEvenly (indices : List Nat) (limit : Nat) : List Nat :=
  if indices.length ≤ limit then indices
  else
    let values := indices.toArray
    (List.range limit).map fun i => values[i * values.size / limit]!

private def checkDetailed (table : Table) (i : Nat) : IO Unit := do
  let row := table.get i
  match row with
  | .split .. => IO.println "Row is split"
  | .certificate id box =>
      IO.println s!"Row {id}:"
      IO.println s!"  box.symmetryIndex = table.symmetryIndex: {decide (box.symmetryIndex = table.symmetryIndex)}"
      IO.println s!"  table.r <= box.r: {decide (table.r ≤ box.r)}"
      IO.println s!"  triangle_valid: {decide (AtlasProjectiveEdgeCertificate.SignedTriangleValid box.root box.triangle)}"
      IO.println s!"  c_nonneg: {decide (0 ≤ box.c)}"
      IO.println s!"  delta_nonneg: {decide (0 ≤ box.δ)}"
      IO.println s!"  r_nonneg: {decide (0 ≤ box.r)}"
      IO.println s!"  B_pos: {decide (∀ j, 0 < (box.certificate j).B)}"
      IO.println s!"  weight_nonneg: {decide (∀ j i, 0 ≤ box.weightLower j i)}"
      IO.println s!"  weight_pos: {decide (∀ j, ∃ i, 0 < box.weightLower j i)}"
      IO.println s!"  support_generators: {decide (∀ j i g, box.supportUpper j i (supportGenerator ((box.certificate j).supportIndex box i) g) ≤ 0)}"
      IO.println s!"  support_boundary: {decide (∀ j i, ((box.certificate j).mix i = 0 ∨ (box.certificate j).mix i = 1000) → ∀ target, box.supportUpper j i target ≤ 0)}"
      IO.println s!"  direction_nonzero: {decide (∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)}"
      IO.println s!"  budget: {decide (∀ j, box.weightBudget j ≤ (box.certificate j).B)}"
      IO.println s!"  variation: {decide (∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)}"
      for j in ([0, 1, 2, 3] : List (Fin 4)) do
        let lhs := box.variationRadiusSum j + 3 * variationError
        let rhs := (box.certificate j).B * box.δ
        IO.println s!"    axis {j.val}: lhs={lhs} <= rhs={rhs} : {decide (lhs ≤ rhs)} (diff={rhs - lhs})"
      IO.println s!"  barycentric: {decide box.barycentricValid}"
      IO.println s!"  angle_bound: {decide (box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2)}"

private def checkIndices (table : Table) (indices : List Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let tasks := indices.map fun i => Task.spawn fun _ =>
    (i, sparseValidIxAtB table.symmetryIndex table.r
      table.get table.size i)
  let results := tasks.map Task.get
  let bad := results.filterMap fun (i, valid) => if valid then none else some i
  unless bad.isEmpty do
    for i in bad do
      checkDetailed table i
    throw (IO.userError s!"invalid sampled rows {bad}")
  let finish ← IO.monoNanosNow
  IO.println (s!"checked {indices.length} local rows in " ++
    s!"{(finish-start)/1000000} ms")

private def parseIndex (value : String) : IO Nat := do
  match value.toNat? with
  | some index =>
      if index < 4 then pure index
      else throw (IO.userError "table index must be 0, 1, 2, or 3")
  | none => throw (IO.userError "table index must be a natural number")

def main (args : List String) : IO Unit := do
  let (indexText, path, sampleText?, rowText?) ← match args with
    | [index, path, sample] =>
        pure (index, path, some sample, (none : Option String))
    | [index, path, "row", row] =>
        pure (index, path, (none : Option String), some row)
    | _ => throw (IO.userError (
        "expects TABLE_INDEX PACK SAMPLE_COUNT or TABLE_INDEX PACK row ROW"))
  let index ← parseIndex indexText
  let packed ← IO.FS.readFile path
  let decodeStart ← IO.monoNanosNow
  let table := PackedLocalViewTree.decodePackedTable index packed
  let firstId := (table.get 0).id
  unless firstId = 0 do
    throw (IO.userError "decoded table has an invalid first row")
  let decodeFinish ← IO.monoNanosNow
  IO.println (s!"decoded {table.size} local rows in " ++
    s!"{(decodeFinish-decodeStart)/1000000} ms")
  (← IO.getStdout).flush
  let indices ← match sampleText?, rowText? with
    | some sampleText, none =>
        match sampleText.toNat? with
        | some sample =>
            if 0 < sample then
              pure (sampleEvenly (certificateIndices table) sample)
            else throw (IO.userError "sample count must be positive")
        | none => throw (IO.userError "sample count must be a natural number")
    | none, some rowText =>
        match rowText.toNat? with
        | some row => pure [row]
        | none => throw (IO.userError "row must be a natural number")
    | _, _ => throw (IO.userError "invalid row selection")
  checkIndices table indices
