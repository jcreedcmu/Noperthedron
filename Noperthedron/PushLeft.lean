import Mathlib.Tactic
import Lean.Elab.Tactic.Location

open Lean.Parser.Tactic

syntax "push_left" (ppSpace location)? : tactic

macro_rules
| `(tactic| push_left $[at $location]?) =>
  `(tactic| (rw [← sub_eq_zero] $[at $location]?; ring_nf -failIfUnchanged $[at $location]?))

syntax "push_lefta" ident : tactic

macro_rules
| `(tactic| push_lefta $h) =>
  `(tactic| (push_left at $h ⊢; exact $h))
