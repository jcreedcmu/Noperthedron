import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.List.Monad

/--
Witness count prod means "there exist `count` many numbers, all ≥ 2,
whose product is prod".
-/
inductive Witness : (count : ℕ) → (prod : ℕ) → Type where
  | leaf : (n : ℕ) → n ≥ 2 → Witness 1 n
  | node : {ca cb pa pb : ℕ} → Witness ca pa → Witness cb pb → Witness (ca + cb) (pa * pb)

def t2 : Witness 1 2 := .leaf 2 (Nat.AtLeastTwo.prop)
def t4 : Witness 2 4 := .node t2 t2
def t5 : Witness 1 5 := .leaf 5 (Nat.AtLeastTwo.prop)
def t25 : Witness 2 25 := .node t5 t5
def t100 : Witness 4 100 := .node t4 t25

open Lean Elab Command

/-
An elaborator that reads in a file and parses it, creating lean decls in response
-/
elab "#mkfoo" : command => do
  let ty  : Expr := mkConst ``Nat

  let dataPath : System.FilePath := "raw-data.txt"
  if (!(← System.FilePath.pathExists dataPath)) then
    throwError "Path '{dataPath}' relative to project root does not exist"
  let contents ← IO.FS.readFile dataPath
  let nums : List ℕ := do
    let item ← contents.splitOn "\n" |> List.filter fun x => x != ""
    item.toNat?.toList

  logInfo m!"File contents := {nums}"
  let mut x : Nat := 0
  for num in nums do
    x := x + 1
    let name := Lean.Name.mkStr2 "foo" (toString x)
    let val : Expr := mkNatLit num
    let decl : Declaration := Declaration.defnDecl {
      name        := name,
      levelParams := [],
      type        := ty,
      value       := val,
      hints       := ReducibilityHints.opaque
      safety      := DefinitionSafety.safe
    }
    liftTermElabM (do
      addDecl decl
      compileDecl decl)

    let valStr ← liftTermElabM (PrettyPrinter.ppExpr val)
    let tyStr ← liftTermElabM (PrettyPrinter.ppExpr ty)
    logInfo m!"declared `{name}` := {valStr} : {tyStr}"

#mkfoo

def z := foo.«1» + foo.«2» + foo.«3»
#eval z
