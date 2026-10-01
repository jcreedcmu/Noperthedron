import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree

/-! Time the fields of `Box.ViewValid` separately on sampled certificate rows.
Usage: bench_fields <file.pack> <samples> -/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView
open Noperthedron.Nopert229.AtlasProjectiveEdgeCertificate

def timeIt (label : String) (acc : IO.Ref (List (String × Nat))) (f : Unit → Bool) : IO Bool := do
  let t0 ← IO.monoNanosNow
  let b ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  acc.modify fun l => (label, t1 - t0) :: l
  return b

def main (args : List String) : IO Unit := do
  let table := PackedLocalViewTree.decodePackedCodeTriangle (← IO.FS.readBinFile args[0]!)
  let samples := (args[1]!).toNat!
  let stride := max 1 (table.size / samples)
  let acc ← IO.mkRef ([] : List (String × Nat))
  let mut n := 0
  let mut i := 0
  while i < table.size do
    match table.get i with
    | .certificate _ box =>
      n := n + 1
      let _ ← timeIt "triangle_valid" acc fun _ => decide (SignedTriangleValid box.root box.triangle)
      let _ ← timeIt "B_pos" acc fun _ => decide (∀ j, 0 < (box.certificate j).B)
      let _ ← timeIt "weight_nonneg" acc fun _ => decide (∀ j i, 0 ≤ box.weightLower j i)
      let _ ← timeIt "weight_pos" acc fun _ => decide (∀ j, ∃ i, 0 < box.weightLower j i)
      let _ ← timeIt "support" acc fun _ => decide (∀ j i k, box.supportUpper j i k ≤ 0)
      let _ ← timeIt "direction_nonzero" acc fun _ => decide (∀ j i,
        box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
      let _ ← timeIt "budget" acc fun _ => decide (∀ j, box.weightBudget j ≤ (box.certificate j).B)
      let _ ← timeIt "variation" acc fun _ => decide (∀ j,
        box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
      let _ ← timeIt "barycentric" acc fun _ => decide box.barycentricValid
      let _ ← timeIt "angle_bound" acc fun _ => decide (box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2)
      let _ ← timeIt "ViewValid (all)" acc fun _ => decide box.ViewValid
    | _ => pure ()
    i := i + stride
  let l ← acc.get
  let labels := ["triangle_valid", "B_pos", "weight_nonneg", "weight_pos", "support",
    "direction_nonzero", "budget", "variation", "barycentric", "angle_bound", "ViewValid (all)"]
  IO.println s!"{n} certificate rows"
  for lab in labels do
    let tot := (l.filter (·.1 == lab)).foldl (fun s p => s + p.2) 0
    IO.println s!"  {lab}: {tot / 1000000 / max n 1} ms/row"
