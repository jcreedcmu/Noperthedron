import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.PackedSolutionTree

/-!
Times the pieces of `AtlasProjectiveGlobalCertificate.Box.Valid` on the
`projectiveGlobal` rows of a 5D pack (single-threaded), to find where Lean's
row check spends its time.

Usage: bench_global_box <chart> <pack> <code-pack manifest.txt> [max rows]
-/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveSolutionTree

def timeIt (label : String) (boxes : Array AtlasProjectiveGlobalCertificate.Box)
    (f : AtlasProjectiveGlobalCertificate.Box → Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut ok := 0
  for b in boxes do
    if (← IO.lazyPure fun _ => f b) then ok := ok + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / 1000 / boxes.size} us/box ({ok} true)"

def main (args : List String) : IO UInt32 := do
  let (chartStr, packPath, manifestPath, maxRows) ← match args with
    | [c, p, m] => pure (c, p, m, 200)
    | [c, p, m, n] => pure (c, p, m, n.toNat!)
    | _ => throw (IO.userError "usage: bench_global_box <chart> <pack> <manifest> [max rows]")
  let chart : CayleyAtlas.ChartIndex := ⟨chartStr.toNat! % 4, by omega⟩
  let packed ← IO.FS.readFile packPath
  -- The certificate rows do not use the identity-tube tables.
  let table := PackedSolutionTree.decodeTable chart #[] packed
  let _ := manifestPath
  let mut boxes : Array AtlasProjectiveGlobalCertificate.Box := #[]
  for i in [0 : table.size] do
    if boxes.size < maxRows then
      match table.get i with
      | .projectiveGlobal _ box => boxes := boxes.push box
      | _ => pure ()
  IO.println s!"{boxes.size} projectiveGlobal boxes"
  timeIt "Valid" boxes fun b => decide b.Valid
  timeIt "Admissible" boxes fun b => decide b.Admissible
  timeIt "bernsteinDisplacementLower" boxes fun b => decide (0 ≤ b.bernsteinDisplacementLower)
  timeIt "adjustedDisplacementBall" boxes fun b =>
    decide (0 ≤ b.adjustedDisplacementBall.center - b.adjustedDisplacementBall.radius)
  timeIt "weightedDefectUpper" boxes fun b => decide (0 ≤ b.weightedDefectUpper)
  timeIt "contactQuadratic x9" boxes fun b =>
    decide (0 ≤ (List.finRange 3).foldl (fun acc i => (List.finRange 3).foldl
      (fun acc c => acc + (b.contactQuadratic i c).c0) acc) 0)
  timeIt "edgeQ x3" boxes fun b =>
    decide (0 ≤ (List.finRange 3).foldl (fun acc i => acc + b.certificate.edgeQ i 0) 0)
  timeIt "viewControlQuadratic x9 (build only)" boxes fun b =>
    decide (0 ≤ (List.finRange 3).foldl (fun acc i => (List.finRange 3).foldl
      (fun acc j => acc + (b.viewControlQuadratic i j).c0) acc) 0)
  timeIt "adjustedViewDisplacementQuadratic x1" boxes fun b =>
    decide (0 ≤ (b.adjustedViewDisplacementQuadratic (b.triangle 0)).c0)
  timeIt "supportAt x1" boxes fun b => decide (0 ≤ b.localShell.supportAt 0 0 0 0)
  timeIt "weightedSupportUpper x1" boxes fun b => decide (0 ≤ b.weightedSupportUpper 0 0)
  timeIt "contactDefectUpper x1" boxes fun b => decide (0 ≤ b.contactDefectUpper 0)
  return 0
