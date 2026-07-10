import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# Fuel-based Newton upper bound for `Nat.sqrt`

The kernel has no acceleration for `Nat.sqrt`: reducing it costs ~70
division steps (~1.4 ms at the checkers' input sizes). The fast checkers
only ever need an *upper* bound on `Nat.sqrt n + 1` (every square root in
the certificates sits on the bound/denominator side of its comparison), so
they use `newtonSqrtUp`: a fixed number of Newton steps from a fixed,
scale-appropriate starting point — ~6 divisions instead of ~70.

Each step maps `g ↦ (g + n / g) / 2 + 1`; the `+1` keeps the iterate
positive (so the next division is meaningful) and costs nothing since only
an upper bound is needed. The invariant is one-sided and unconditional in
the start value: every iterate dominates `Nat.sqrt n`
(`newtonSqrtUp_ge_sqrt`), by the discrete AM–GM argument
`n < g·(n/g + 1) ≤ g·(2s - g) ≤ s²` for any would-be violation.
-/

namespace Noperthedron.NewtonSqrt

/-- One guarded Newton step. -/
def step (n g : ℕ) : ℕ := (g + n / g) / 2 + 1

/-- `fuel` Newton steps from `g`. -/
def iter (n : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | fuel + 1, g => iter n fuel (step n g)

/-- `newtonSqrtUp n fuel start` dominates `Nat.sqrt n` whenever `start`
does (see `newtonSqrtUp_ge_sqrt`). -/
def newtonSqrtUp (n fuel start : ℕ) : ℕ := iter n fuel start

/-- Discrete AM–GM: a positive `g` cannot Newton-step below any `s` with
`s * s ≤ n`. (Else `g + n/g ≤ 2s - 1` and
`n < g·(n/g + 1) ≤ g·(2s - g) ≤ s² ≤ n`.) -/
private lemma le_step {n g s : ℕ} (hg : 0 < g) (hs : s * s ≤ n) :
    s ≤ step n g := by
  unfold step
  by_contra hlt
  rw [not_le] at hlt
  have h2 : g + n / g < 2 * s := by omega
  have hdivmod := Nat.div_add_mod n g
  have hmod : n % g < g := Nat.mod_lt n hg
  have hn' : n < g * (n / g) + g := by linarith
  have hn : (n : ℤ) < (g : ℤ) * ((n / g : ℕ) : ℤ) + g := by exact_mod_cast hn'
  have h2' : (g : ℤ) + ((n / g : ℕ) : ℤ) < 2 * s := by exact_mod_cast h2
  have hq : ((n / g : ℕ) : ℤ) + 1 ≤ 2 * s - g := by linarith
  have hmul : (g : ℤ) * (((n / g : ℕ) : ℤ) + 1) ≤ (g : ℤ) * (2 * s - g) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hsq := sq_nonneg ((g : ℤ) - s)
  have hsZ : (s : ℤ) * s ≤ n := by exact_mod_cast hs
  linarith

/-- Every iterate of a positive start dominates any `s` with `s * s ≤ n`;
in particular it dominates `Nat.sqrt n`. -/
private lemma le_iter {n s : ℕ} (hs : s * s ≤ n) :
    ∀ (fuel : ℕ) {g : ℕ}, 0 < g → s ≤ g → s ≤ iter n fuel g
  | 0, _, _, hsg => hsg
  | fuel + 1, g, hg, _ => by
    have hstep : s ≤ step n g := le_step hg hs
    exact le_iter hs fuel (Nat.succ_le_succ (Nat.zero_le _)) hstep

/-- The soundness interface: from any starting point at least
`Nat.sqrt n` (and positive), the result still dominates `Nat.sqrt n`. -/
theorem newtonSqrtUp_ge_sqrt {n fuel start : ℕ} (hstart : 0 < start)
    (h : Nat.sqrt n ≤ start) : Nat.sqrt n ≤ newtonSqrtUp n fuel start :=
  le_iter (by simpa [Nat.pow_two] using Nat.sqrt_le' n) fuel hstart h

end Noperthedron.NewtonSqrt
