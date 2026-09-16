import Noperthedron.Nopert229.PackedSolutionTree

/-!
# Native timing audit for Nopert #229 global leaves

This is deliberately not a proof constructor.  It reads a benchmark pack
made from a live checkpoint with `--fill-pending`, selects only resolved
terminal rows, and times the exact Boolean predicate used by the final native
executable.  Pending placeholders and structural rows are never checked.
Shared-local tube rows are omitted because a live global checkpoint pack does
not include the separate local tables they require.
-/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree

private def rowKind? : Row → Option String
  | .projective .. => some "edge"
  | .projectiveGlobal .. => some "global"
  | .projectiveMixedGlobal .. => some "mixed-global"
  | .projectiveLocal .. => some "local"
  | .symmetryLocal .. => some "symmetry-local"
  | .symmetryTube .. => some "symmetry-tube"
  | .radiusPrune .. => some "radius"
  | .fundamentalPrune .. => some "fundamental"
  | _ => none

private def sampleEvenly (indices : List Nat) (limit : Nat) : List Nat :=
  if indices.length ≤ limit then indices
  else
    let values := indices.toArray
    (List.range limit).map fun i => values[i * values.size / limit]!

private def indicesOfKind (table : Table) (kind : String) : List Nat :=
  (List.range table.size).filter fun i => rowKind? (table.get i) = some kind

private def checkKind (table : Table) (kind : String) (limit : Nat) : IO Unit := do
  let all := indicesOfKind table kind
  let indices := sampleEvenly all limit
  if indices.isEmpty then
    IO.println s!"{kind}: no rows"
    return
  let start ← IO.monoNanosNow
  let tasks := indices.map fun i =>
    Task.spawn fun _ =>
      (i, validIxAtB table.chart table.get table.size table.sharedLocal i)
  let results := tasks.map Task.get
  let bad := results.filterMap fun (i, valid) => if valid then none else some i
  unless bad.isEmpty do
    throw (IO.userError s!"{kind}: invalid sampled rows {bad}")
  let finish ← IO.monoNanosNow
  IO.println (s!"{kind}: checked {indices.length}/{all.length} rows in " ++
    s!"{(finish - start) / 1000000} ms")
  (← IO.getStdout).flush

private def checkRow (table : Table) (index : Nat) : IO Unit := do
  unless index < table.size do
    throw (IO.userError s!"row {index} is outside table of size {table.size}")
  let start ← IO.monoNanosNow
  let valid := validIxAtB table.chart table.get table.size table.sharedLocal index
  let finish ← IO.monoNanosNow
  unless valid do
    let row := table.get index
    match row with
    | .projectiveGlobal _ box =>
        IO.println s!"Diagnostics for projectiveGlobal row {index}:"
        IO.println s!"  triangle_valid: {decide (AtlasProjectiveEdgeCertificate.SignedTriangleValid box.root box.triangle)}"
        IO.println s!"  weight_nonneg: {decide (∀ i, 0 ≤ box.weightLower i)}"
        IO.println s!"  weight_pos: {decide (∃ i, 0 < box.weightLower i)}"
        IO.println s!"  direction_nonzero: {decide (∀ i, box.supportUpper i (box.certificate.nonzeroWitness i) < 0)}"
        IO.println s!"  ball_multiplier_nonneg: {decide (0 ≤ box.ballMultiplier)}"
        IO.println s!"  interval min: x={box.interval.min.x}, y={box.interval.min.y}, z={box.interval.min.z}"
        IO.println s!"  interval max: x={box.interval.max.x}, y={box.interval.max.y}, z={box.interval.max.z}"
        IO.println s!"  triangle: ({box.triangle 0 0}, {box.triangle 0 1}, {box.triangle 0 2}) - ({box.triangle 1 0}, {box.triangle 1 1}, {box.triangle 1 2}) - ({box.triangle 2 0}, {box.triangle 2 1}, {box.triangle 2 2})"
        IO.println s!"  innerIndex: {box.innerIndex 0}, {box.innerIndex 1}, {box.innerIndex 2}"
        IO.println s!"  cert B: {box.certificate.B}"
        IO.println s!"  cert edgeStart: {box.certificate.edgeStart 0}, {box.certificate.edgeStart 1}, {box.certificate.edgeStart 2}"
        IO.println s!"  cert edgeFinish: {box.certificate.edgeFinish 0}, {box.certificate.edgeFinish 1}, {box.certificate.edgeFinish 2}"
        IO.println s!"  cert mix: {box.certificate.mix 0}, {box.certificate.mix 1}, {box.certificate.mix 2}"
        IO.println s!"  cert nonzeroWitness: {box.certificate.nonzeroWitness 0}, {box.certificate.nonzeroWitness 1}, {box.certificate.nonzeroWitness 2}"
        IO.println s!"  adjustedDisplacementBall: center={box.adjustedDisplacementBall.center}, radius={box.adjustedDisplacementBall.radius}"
        IO.println s!"  ball lower (center - radius): {box.adjustedDisplacementBall.center - box.adjustedDisplacementBall.radius}"
        IO.println s!"  bernsteinDisplacementLower: {box.bernsteinDisplacementLower}"
    | .projectiveMixedGlobal _ _ =>
        IO.println s!"Row {index} is projectiveMixedGlobal"
    | .radiusPrune id interval _ =>
        IO.println s!"Diagnostics for radiusPrune row {index}:"
        IO.println s!"  id: {id}"
        IO.println s!"  interval min: x={interval.min.x}, y={interval.min.y}, z={interval.min.z}"
        IO.println s!"  interval max: x={interval.max.x}, y={interval.max.y}, z={interval.max.z}"
        IO.println s!"  outsideCayleyBall: {decide interval.outsideCayleyBall}"
        let minSq := minAbsBound interval.min.x interval.max.x ^ 2 +
          minAbsBound interval.min.y interval.max.y ^ 2 +
          minAbsBound interval.min.z interval.max.z ^ 2
        IO.println s!"  minAbsBound sum of squares: {minSq} (needs > 3)"
    | _ =>
        IO.println s!"Row {index} has kind {rowKind? row}"
    throw (IO.userError s!"row {index} is invalid")
  IO.println (s!"row {index} ({rowKind? (table.get index)}): valid in " ++
    s!"{(finish - start) / 1000000} ms")

private def parseChart (value : String) : IO CayleyAtlas.ChartIndex := do
  match value.toNat? with
  | some 0 => pure 0
  | some 1 => pure 1
  | some 2 => pure 2
  | _ => throw (IO.userError "chart must be 0, 1, or 2")

def main (args : List String) : IO Unit := do
  let (chartText, path, selection, rowMode, targetKind?) ← match args with
    | [chart, path, "row", index] => pure (chart, path, index, true, none)
    | [chart, path, limit, kind] => pure (chart, path, limit, false, some kind)
    | [chart, path, limit] => pure (chart, path, limit, false, none)
    | _ => throw (IO.userError
        "expects CHART PACK SAMPLE_COUNT [KIND] or CHART PACK row ROW")
  let chart ← parseChart chartText
  let selected ← match selection.toNat? with
    | some limit =>
        if 0 < limit then pure limit
        else if rowMode then pure 0
        else throw (IO.userError "sample count must be positive")
    | none => throw (IO.userError "selection must be a natural number")
  let packed ← IO.FS.readFile path
  let shared : SharedLocalTables := fun _ => none
  let table := PackedSolutionTree.decodeTable chart shared packed
  IO.println s!"decoded benchmark chart {chart}: {table.size} rows"
  (← IO.getStdout).flush
  if rowMode then
    checkRow table selected
    return
  let kinds := match targetKind? with
    | some k => [k]
    | none => ["edge", "global", "mixed-global", "local",
        "symmetry-local", "radius", "fundamental"]
  for kind in kinds do
    checkKind table kind selected
