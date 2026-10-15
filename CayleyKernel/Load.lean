module

public import Lean
public import Cayley.Checker.KTree
public meta import Lean
public meta import Cayley.Checker.KTree

@[expose] public section

/-!
# Elaboration-time loading of the kernel certificate

`cayley_chunks "file"` reads a chunk file (one chunk per line:
`id chart face K c₀ … c₄ h₀ … h₄ tokens…`, tokens `S<d>`, `D<code>`, `G<s>:<w₀>:<w₁>`, `H`)
and, for each chunk, adds `B_id : KBox`, `T_id : KTree` and the theorem
`ok_id : kCheck false B_id T_id = true`, proved by `Eq.refl true` (the kernel evaluates the check).
Nothing here is trusted: the kernel only accepts true statements about whatever terms were
built. `cayley_root` assembles one root box from its skeleton and chunks.
-/

namespace Cayley.KLoad

open Lean Meta Elab Cayley.K

meta section

def natE (n : Nat) : Expr := mkRawNatLit n

def intE : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (natE n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (natE n)

def listIntE (l : List Int) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Int) (intE x) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Int))

def boxE (chart face K : Nat) (c h : List Int) : Expr :=
  mkAppN (mkConst ``KBox.mk) #[natE chart, natE face, natE K, listIntE c, listIntE h]

def parseIntS (s : String) : Int :=
  if s.startsWith "-" then -((s.drop 1).toString.toNat! : Int) else (s.toNat! : Int)

/-- Build the tree `Expr` from tokens starting at `i`. -/
partial def treeE (toks : Array String) (i : Nat) : Expr × Nat :=
  let t := toks[i]!
  let c := t.front
  let rest := (t.drop 1).toString
  if c == 'S' then
    let (l, j) := treeE toks (i + 1)
    let (r, k) := treeE toks j
    (mkApp3 (mkConst ``KTree.split) (natE rest.toNat!) l r, k)
  else if c == 'D' then (mkApp (mkConst ``KTree.dom) (natE rest.toNat!), i + 1)
  else if c == 'G' then
    match rest.splitOn ":" with
    | [s, w0, w1] =>
      (mkApp3 (mkConst ``KTree.gap) (natE s.toNat!) (intE (parseIntS w0)) (intE (parseIntS w1)), i + 1)
    | _ => (mkConst ``KTree.hole, i + 1)
  else (mkConst ``KTree.hole, i + 1)

def reflTrueE : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

def eqTrueE (lhs : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs (mkConst ``Bool.true)

def addDef (nm : Name) (ty val : Expr) : CoreM Unit := do
  withExporting <| addDecl <| .defnDecl {
    name := nm, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe }
  modifyEnv (addNoncomputable · nm)

def addThm (nm : Name) (ty val : Expr) : CoreM Unit := do
  withExporting <| addDecl <| .thmDecl { name := nm, levelParams := [], type := ty, value := val }

def chunkName (ns : Name) (pre : String) (id : Nat) : Name := ns ++ Name.mkSimple s!"{pre}_{id}"

elab "cayley_chunks " path:str : command => do
  let ns ← getCurrNamespace
  let txt ← IO.FS.readFile path.getString
  let mut n := 0
  let mut tot := 0
  let mut worst := 0
  let mut worstId := 0
  for line in txt.splitOn "\n" do
    let toks := ((line.splitOn " ").filter (· ≠ "")).toArray
    if toks.size < 15 then continue
    let id := toks[0]!.toNat!
    let nums := (toks.extract 1 14).map parseIntS
    let b := boxE nums[0]!.toNat nums[1]!.toNat nums[2]!.toNat (nums.extract 3 8).toList
      (nums.extract 8 13).toList
    let (t, _) := treeE (toks.extract 14 toks.size) 0
    let bn := chunkName ns "B" id
    let tn := chunkName ns "T" id
    let t0 ← IO.monoMsNow
    Command.liftCoreM do
      addDef bn (mkConst ``KBox) b
      addDef tn (mkConst ``KTree) t
      addThm (chunkName ns "ok" id)
        (eqTrueE (mkApp3 (mkConst ``kCheck) (mkConst ``Bool.false) (mkConst bn) (mkConst tn))) reflTrueE
    let dt := (← IO.monoMsNow) - t0
    n := n + 1
    tot := tot + dt
    if dt > worst then
      worst := dt
      worstId := id
  logInfo m!"cayley_chunks: {n} chunks, {tot} ms, worst {worst} ms (chunk {worstId})"

/-- `cayley_root r "skel"`: the skeleton file holds the root's tokens (holes `H`) on line 1
and the hole chunk ids on line 2. Adds `S_r`, `skel_r : kCheck true (rootK r) S_r = true`,
`holes_r : holes (rootK r) S_r = [B_…]` and `all_r : AllOK [(B_…, T_…), …]`. -/
elab "cayley_root " r:num path:str : command => do
  let ns ← getCurrNamespace
  let root := r.getNat
  let txt ← IO.FS.readFile path.getString
  let lines := txt.splitOn "\n"
  let toks := ((lines[0]!.splitOn " ").filter (· ≠ "")).toArray
  let ids := ((lines[1]!.splitOn " ").filter (· ≠ "")).map String.toNat!
  let (t, _) := treeE toks 0
  let sn := chunkName ns "S" root
  let boxTy := mkConst ``KBox
  let pairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) boxTy (mkConst ``KTree)
  let rootE := mkApp (mkConst ``rootK) (natE root)
  let boxList := ids.foldr (fun id acc => mkApp3 (mkConst ``List.cons [Level.zero]) boxTy
    (mkConst (chunkName ns "B" id)) acc) (mkApp (mkConst ``List.nil [Level.zero]) boxTy)
  let pairList := ids.foldr (fun id acc => mkApp3 (mkConst ``List.cons [Level.zero]) pairTy
    (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) boxTy (mkConst ``KTree)
      (mkConst (chunkName ns "B" id)) (mkConst (chunkName ns "T" id))) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) pairTy)
  -- AllOK proof: nested And.intro of the chunk theorems
  let allPf := ids.foldr (fun id (acc : Expr × Expr) =>
    let stmt := eqTrueE (mkApp3 (mkConst ``kCheck) (mkConst ``Bool.false) (mkConst (chunkName ns "B" id))
      (mkConst (chunkName ns "T" id)))
    (mkApp4 (mkConst ``And.intro) stmt acc.2 (mkConst (chunkName ns "ok" id) ) acc.1,
     mkApp2 (mkConst ``And) stmt acc.2))
    (mkConst ``True.intro, mkConst ``True)
  let t0 ← IO.monoMsNow
  Command.liftCoreM do
    addDef sn (mkConst ``KTree) t
    addThm (chunkName ns "skel" root) (eqTrueE (mkApp3 (mkConst ``kCheck) (mkConst ``Bool.true) rootE (mkConst sn)))
      reflTrueE
    let holesE := mkApp2 (mkConst ``holes) rootE (mkConst sn)
    addThm (chunkName ns "holes" root)
      (mkApp3 (mkConst ``Eq [Level.one]) (mkApp (mkConst ``List [Level.zero]) boxTy) holesE boxList)
      (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkApp (mkConst ``List [Level.zero]) boxTy) boxList)
    addThm (chunkName ns "all" root) (mkApp (mkConst ``AllOK) pairList) allPf.1
  logInfo m!"cayley_root {root}: {ids.length} chunks, {(← IO.monoMsNow) - t0} ms"

end

end Cayley.KLoad

end
