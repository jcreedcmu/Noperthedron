module

public import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.SyntheticMVars

public section

/-!
# Numerals computed at elaboration time

`eval_nat% e` evaluates the closed term `e : Nat` and elaborates to the resulting numeral.
The checker uses it for tables that are given by a formula but that the kernel should see as
literals, so that it does not recompute them on every use.

Nothing here is trusted: the result is an ordinary numeral, and the soundness proofs check
it against the formula.
-/

namespace Cayley.K

open Lean Meta Elab Term

/-- `eval_nat% e` is the numeral that the closed term `e : Nat` evaluates to. -/
syntax (name := evalNatStx) "eval_nat% " term : term

@[term_elab evalNatStx] meta def elabEvalNat : TermElab := fun stx _ => do
  let e ← elabTermEnsuringType stx[1] (mkConst ``Nat)
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← ofExceptKernelException (Kernel.whnf (← getEnv) {} e)
  let some n := v.rawNatLit? | throwError "eval_nat%: not a numeral:{indentExpr v}"
  return mkNatLit n

end Cayley.K

end
