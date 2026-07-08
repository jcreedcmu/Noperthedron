import Lake.CLI.Main

/-!
Vendored, patched copy of https://github.com/PatrickMassot/checkdecls.

The upstream version imports the roots of *every* `lean_lib` in the root
package, which fails when the build-on-demand libraries (`VerifiedNative`,
`VerifiedKernel` — deliberately kept out of `defaultTargets` so CI never pays
for them) have not been built. This copy imports only the libraries listed in
`defaultTargets` — i.e. it checks the blueprint's declarations against what
CI actually builds — and falls back to upstream behavior when
`defaultTargets` names no library.

Because this executable is defined in the root package under the same name,
`lake exe checkdecls` resolves to it rather than to the dependency's.
-/

open Lake Lean

unsafe def main (args : List String) : IO UInt32 := do
  unless args.length == 1 do
    println! "This command takes exactly one argument: the path to a file containing a list of declarations to check."
    return 1
  let filename : System.FilePath := args[0]!
  unless ← filename.pathExists do
    println! "Could not find declaration list {filename}."
    return 1
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let (ws?, log) ← (loadWorkspace config).run?
  log.replay (logger := .stderr)
  let some ws := ws? | return 1
  let defaultLibs := ws.root.leanLibs.filter fun lib =>
    ws.root.defaultTargets.contains lib.name
  let libs := if defaultLibs.isEmpty then ws.root.leanLibs else defaultLibs
  let imports := libs.flatMap (·.config.roots.map fun module => { module })
  -- see comments in https://github.com/leanprover/lean4/pull/6325
  enableInitializersExecution
  let env ← Lean.importModules imports {}
  let mut ok := true
  for line in ← IO.FS.lines filename do
    unless env.contains line.toName do
      println! "{line} is missing."
      ok := false
  return if ok then 0 else 1
