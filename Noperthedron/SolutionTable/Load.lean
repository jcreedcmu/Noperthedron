import Lean
import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Parse

/-!
# Elaboration-time CSV ingestion for kernel-only checking

The kernel-only verification route (see `kernel-decide-note.md`) needs the
solution-table rows as Lean *term literals*: in-kernel `String` parsing is
hopeless (~9 s per 300 bytes), and generating literals as `.lean` source files
would push gigabytes through the parser and term elaborator.

This module takes a third route: parse the CSV **during elaboration**. The
`load_csv_rows` command reads the CSV with `IO`, parses a row range with the
existing (untrusted) `parseRowCsv`, builds kernel-friendly `Expr` literals for
the rows directly — no surface syntax, no term elaboration — and adds a single
chunk definition `csvRows_<a>_<b> : List Row` via `addDecl`.

The command only *loads*. Validation is stated separately, as ordinary source
theorems about the loaded definitions proved by `decide +kernel` (so the
kernel performs the whole evaluation — no `ofReduceBool`, no compiler):

* leaf checks, e.g. `csvRows_a_b.all Row.leafOk = true`;
* split checks, stated against whatever table view is in scope (see
  `scripts/test_csv_load.lean` for a mini-table demonstration);
* eventually the bridging lemmas that assemble a `ValidTable`.

Nothing here needs to be trusted: the parser and `Expr` builders can be
arbitrarily buggy and the kernel will still only accept true statements about
whatever rows were actually constructed. Faithfulness to the CSV is not part
of the trusted base for the same reason the runtime parser isn't — every
property the final proof needs is checked downstream, on the constructed rows.
-/

namespace Noperthedron.Solution

/-- Leaf-row validity as a `Bool`: global leaves (`nodeType = 1`) must satisfy
`Row.ValidGlobal`, local leaves (`nodeType = 2`) must satisfy `Row.ValidLocal`,
and other rows (structural splits, checked against the full table elsewhere)
pass vacuously. -/
def Row.leafOk (r : Row) : Bool :=
  if r.nodeType = 1 then decide r.ValidGlobal
  else if r.nodeType = 2 then decide r.ValidLocal
  else true

namespace Load

open Lean Meta Elab

/-- Cached `Expr`s that are shared by every row literal (types, instances, and
the two possible `sigma_Q` values), so per-row construction does no instance
synthesis. -/
structure Ctx where
  poseQ : Expr
  leInst : Expr
  /-- `fun x y : Pose ℚ => (inst : Decidable (x ≤ y))`, applied per interval. -/
  dle : Expr
  sigma0 : Expr
  sigma1 : Expr

def natE (n : ℕ) : Expr := mkRawNatLit n

def intE : ℤ → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (natE n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (natE n)

/-- A rational literal as `mkRat num den`. The kernel normalizes it with one
(GMP-fast) gcd on first use, memoized within each declaration. -/
def ratE (q : ℚ) : Expr := mkApp2 (mkConst ``mkRat) (intE q.num) (natE q.den)

def reflTrueE : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- `of_decide_eq_true (Eq.refl true) : prop` — the kernel certifies it by
reducing `decide prop` to `true`. -/
def decideProofE (prop inst : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) prop inst reflTrueE

def finE (n v : ℕ) : Expr :=
  let nE := natE n
  let vE := natE v
  let prop := mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``Nat)
    (mkConst ``instLTNat) vE nE
  let inst := mkApp2 (mkConst ``Nat.decLt) vE nE
  mkApp3 (mkConst ``Fin.mk) nE vE (decideProofE prop inst)

def vertexIndexE (vi : VertexIndex) : Expr :=
  mkApp3 (mkConst ``VertexIndex.mk) (finE 15 vi.k) (finE 2 vi.ℓ) (finE 3 vi.i)

def poseE (p : Pose ℚ) : Expr :=
  mkApp6 (mkConst ``Pose.mk) (mkConst ``Rat)
    (ratE p.θ₁) (ratE p.θ₂) (ratE p.φ₁) (ratE p.φ₂) (ratE p.α)

def intervalE (ctx : Ctx) (iv : Interval) : Expr :=
  let pmin := poseE iv.min
  let pmax := poseE iv.max
  let toProd := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
    ctx.poseQ ctx.poseQ pmin pmax
  let prop := mkApp4 (mkConst ``LE.le [Level.zero]) ctx.poseQ ctx.leInst pmin pmax
  let inst := (mkApp2 ctx.dle pmin pmax).headBeta
  mkApp4 (mkConst ``NonemptyInterval.mk [Level.zero]) ctx.poseQ ctx.leInst
    toProd (decideProofE prop inst)

def rowE (ctx : Ctx) (r : Row) : Expr :=
  mkAppN (mkConst ``Row.mk) #[
    natE r.ID, natE r.nodeType, natE r.nrChildren, natE r.IDfirstChild,
    natE r.split,
    intervalE ctx r.interval,
    vertexIndexE r.S_index,
    intE r.wx_numerator, intE r.wy_numerator, natE r.w_denominator,
    vertexIndexE r.P1_index, vertexIndexE r.P2_index, vertexIndexE r.P3_index,
    vertexIndexE r.Q1_index, vertexIndexE r.Q2_index, vertexIndexE r.Q3_index,
    intE r.r',
    if r.sigma_Q.val = 0 then ctx.sigma0 else ctx.sigma1]

private def elabSigma (n : ℕ) : TermElabM Expr := do
  let stx ← if n = 0 then `((⟨0, by decide⟩ : Finset.Icc (0:ℕ) 1))
            else `((⟨1, by decide⟩ : Finset.Icc (0:ℕ) 1))
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def mkCtx : TermElabM Ctx := do
  let poseQ := mkApp (mkConst ``Pose) (mkConst ``Rat)
  let leInst ← synthInstance (mkApp (mkConst ``LE [Level.zero]) poseQ)
  let dle ← withLocalDeclD `x poseQ fun x => withLocalDeclD `y poseQ fun y => do
    let prop := mkApp4 (mkConst ``LE.le [Level.zero]) poseQ leInst x y
    let inst ← synthInstance (mkApp (mkConst ``Decidable) prop)
    mkLambdaFVars #[x, y] inst
  return { poseQ, leInst, dle, sigma0 := ← elabSigma 0, sigma1 := ← elabSigma 1 }

/-- `load_csv_rows "path.csv" from a to b` reads rows `[a, b)` of the
solution-tree CSV and adds them to the environment as one literal definition
`csvRows_<a>_<b> : List Row`. Loading only — validate the chunk with ordinary
theorems (`by decide +kernel`) about it.

By default the chunk gets no executable code and is marked `noncomputable`
(the kernel route never runs it). With the trailing `compiled` flag the chunk
is instead compiled, so validation theorems may also use `native_decide`. -/
elab "load_csv_rows " path:str " from " a:num " to " b:num
    c:(&"compiled")? : command => do
  let lo := a.getNat
  let hi := b.getNat
  unless lo < hi do throwError "empty row range [{lo}, {hi})"
  let t0 ← IO.monoMsNow
  let csv ← IO.FS.readFile path.getString
  let lines := (csv.splitOn "\n").toArray
  let tRead ← IO.monoMsNow
  let mut rows : Array Row := #[]
  for i in [lo:hi] do
    unless i + 1 < lines.size do
      throwError "row {i} out of range (file has {lines.size - 2} rows)"
    match parseRowCsv lines[i + 1]! with
    | .ok r =>
      unless r.ID = i do throwError "row ID mismatch at {i}: parsed ID {r.ID}"
      rows := rows.push r
    | .error e => throwError "parse error at row {i}: {e}"
  let tParse ← IO.monoMsNow
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let ctx ← mkCtx
    let rowTy := mkConst ``Row
    let listE := rows.foldr
      (fun r acc => mkApp3 (mkConst ``List.cons [Level.zero]) rowTy (rowE ctx r) acc)
      (mkApp (mkConst ``List.nil [Level.zero]) rowTy)
    let chunkNm := ns ++ Name.mkSimple s!"csvRows_{lo}_{hi}"
    addDecl <| .defnDecl {
      name := chunkNm, levelParams := [],
      type := mkApp (mkConst ``List [Level.zero]) rowTy, value := listE,
      hints := .abbrev, safety := .safe }
    if c.isSome then
      compileDecls #[chunkNm]
    else
      -- No executable code (the kernel route never runs the chunk), so mark
      -- it noncomputable for clean downstream errors.
      modifyEnv (addNoncomputable · chunkNm)
    let tDefs ← IO.monoMsNow
    logInfo m!"load_csv_rows [{lo}, {hi}): read {tRead - t0} ms, \
      parse {tParse - tRead} ms, define+check {tDefs - tParse} ms"

end Load

end Noperthedron.Solution
