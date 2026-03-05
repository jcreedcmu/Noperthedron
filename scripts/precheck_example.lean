import Lean
import Noperthedron.SolutionTable.CertificateIO
import Noperthedron.SolutionTable.ExamplePrecheck

open Lean
open Solution

def readJsonFile (path : System.FilePath) : IO Json := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | Except.ok j => pure j
  | Except.error e => throw <| IO.userError e

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "docs/solution_table_certificates.example.json"
  let j ← readJsonFile path
  match Solution.parseTableAndPrecheck j with
  | Except.error e => IO.eprintln s!"parse error: {e}"
  | Except.ok (tab, data, congruence) =>
      let ok := Solution.solutionTablePrecheckBoolWithCongruence tab data congruence
      IO.println (toString ok)
