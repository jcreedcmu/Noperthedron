import Noperthedron.Nopert229.NativeExecutable
import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.IdentityTube

/-!
Compose the per-triangle identity-tube tables into the wedge-wide statement
`IdentityTube.not_translated_rupert_of_tables`.

Usage: `check_identity_tube [--force] <manifest.txt>`, where the manifest lists
the `code_C_tri_K.pack` files in code order (as written by
`export_codetrees_pack`), so that line `t` is `codeTriangles[t]`.

Without `--force`, a table whose `.validated` stamp (from
`validate_code_pack`) says `table.Valid PROVED` is not re-checked; the
triangle/root/symmetry/radius links are always checked. With `--force`
every table is checked here and the final theorem is instantiated in this
process.
-/

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.NativeExecutable
open Noperthedron.Nopert229.IdentityTube
open Noperthedron.Nopert229.WedgeCover

private def taskCount : Nat := 16

private def emptyTable : Table :=
  { symmetryIndex := 0, r := 0, get := fun _ => default, size := 0 }

private def stamped (path : String) : IO Bool := do
  let stampPath := s!"{path}.validated"
  if ← System.FilePath.pathExists stampPath then
    return (← IO.FS.readFile stampPath).containsSubstr "status: table.Valid PROVED"
  return false

/-- Check tables `k, k+1, ...` natively, threading the validity prefix. -/
private partial def validateFrom (paths : Array String) (tables : ℕ → Table) (k : ℕ)
    (hk : ∀ t, t < k → (tables t).Valid) :
    IO (PLift (∀ t, t < paths.size → (tables t).Valid)) := do
  if h : k = paths.size then
    return ⟨h ▸ hk⟩
  else
    let checked ← checkLocal paths[k]! taskCount (tables k)
    validateFrom paths tables (k + 1) (valid_prefix_succ hk checked.down)

def main (args : List String) : IO Unit := do
  let force := args.contains "--force"
  let manifestPath ← match args.filter (· != "--force") with
    | [m] => pure m
    | _ => throw (IO.userError "Usage: check_identity_tube [--force] <manifest.txt>")
  let dir := (System.FilePath.mk manifestPath).parent.getD "."
  let mut paths : Array String := #[]
  for line in ← IO.FS.lines manifestPath do
    if let filename :: _ := line.splitOn " " then
      if filename.endsWith ".pack" then
        paths := paths.push s!"{dir}/{filename}"
  unless paths.size = codeTriangles.size do
    throw (IO.userError s!"manifest has {paths.size} packs but there are {codeTriangles.size} code triangles")
  let mut arr : Array Table := #[]
  let mut unstamped : Array String := #[]
  for path in paths do
    let table := PackedLocalViewTree.decodePackedCodeTriangle (← IO.FS.readBinFile path)
    unless (table.get 0).id = 0 do
      throw (IO.userError s!"{path}: invalid first row id")
    arr := arr.push table
    unless ← stamped path do unstamped := unstamped.push path
  let tables : ℕ → Table := fun t => arr.getD t emptyTable
  let s := (tables 0).symmetryIndex
  let r := (List.range paths.size).foldl (fun m t => min m (tables t).r) (tables 0).r
  unless 0 < r do
    throw (IO.userError s!"nonpositive table radius {r}")
  -- The links between the packs and the wedge cover's triangles.
  if hmatch : TablesMatch tables s r then
    IO.println s!"{paths.size} tables match codeTriangles (root 0, symmetry {s}, min r = {r})"
    if force then
      let hsize ← if h : paths.size = codeTriangles.size then pure (PLift.up h)
        else throw (IO.userError "manifest size mismatch")
      let hvalid ← validateFrom paths tables 0 (fun _ h => absurd h (Nat.not_lt_zero _))
      have hvalid' : ∀ t, t < codeTriangles.size → (tables t).Valid := by
        intro t ht; exact hvalid.down t (by rw [hsize.down]; exact ht)
      let _proof := fun (P : C5Model) => @not_translated_rupert_of_tables P tables s r hmatch hvalid'
      IO.println s!"[IDENTITY TUBE PROVED] all {paths.size} tables checked in this process; tube symmetry {s}, radius {r}"
    else if unstamped.isEmpty then
      IO.println s!"[IDENTITY TUBE] all {paths.size} tables have validate_code_pack stamps; with not_translated_rupert_of_tables this gives tube symmetry {s}, radius {r}"
    else
      IO.println s!"[INCOMPLETE] {unstamped.size} tables not yet validated: {unstamped.toList}"
      IO.Process.exit 1
  else
    throw (IO.userError "tables do not match codeTriangles / symmetry / radius")
