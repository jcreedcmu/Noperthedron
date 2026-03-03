import Noperthedron.SolutionTable.Validity

namespace Solution

/-!
### Bridge lemmas for computational step

These lemmas bridge computable `FromData` Bool checks to the noncomputable `CheckBool` functions
needed by `Table.Precheck` and ultimately `Table.Valid`.
-/

/-- Computable congruence check wrapper. -/
def congrDecide (row : Row) : Bool := decide row.localCongruenceIndexCheck

theorem congrDecide_sound (row : Row) :
    congrDecide row = true → row.localCongruenceIndexCheck :=
  fun h => of_decide_eq_true h

/-!
### FromData → CheckBool bridges

The `FromData` versions compute pure `&&`-chains over the certificate data arrays, while the
`CheckBool` versions go through `decide` of a `Prop` spec (with a `classical` Decidable instance
for global) or through an alg-based `&&`-chain (for local). The bridge shows that if `FromData`
returns `true`, so does `CheckBool`.

Key insight: when the alg is `cert.toAlg` (global) or `ofOracle (toOracle cert)` (local),
the alg field accesses (e.g., `cert.toAlg.exceeds row`) reduce definitionally to the same
`oracleGet cert.data.X_ok row.ID` used by `FromData`. So both sides check identical atoms —
only the `&&` grouping differs.
-/

/-- Bridge: FromData global check implies alg-based global check.
Both sides check the same five atoms; `FromData` uses left-associated `&&`,
while `CheckBool` uses `decide` of a right-associated `∧` spec. -/
theorem globalFromData_imp_globalCheckBool (row : Row)
    {tab : Table} (cert : GlobalPrecheckCertificate tab) :
    row.globalPreconditionCheckBoolFromData cert.data = true →
    row.globalPreconditionCheckBool cert.toAlg = true := by
  intro h
  -- Extract the five Bool atoms from the left-associated &&-chain
  simp only [Row.globalPreconditionCheckBoolFromData, Bool.and_eq_true,
    decide_eq_true_eq] at h
  -- h : (((nodeType = 1 ∧ four = true) ∧ eps = true) ∧ w = true) ∧ exc = true
  -- Build the Prop spec and use decide_eq_true
  unfold Row.globalPreconditionCheckBool
  rw [decide_eq_true_eq]
  -- Goal: globalPreconditionCheckSpec cert.toAlg
  -- cert.toAlg.exceeds row reduces to oracleGet cert.data.exceeds_ok row.ID
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Bridge: FromData local check implies alg-based local check.
Both sides check the same eleven atoms; only the `&&` grouping differs.
The alg field accesses (via `ofOracle ∘ toOracle`) reduce definitionally
to the same `oracleGet` calls used by `FromData`. -/
theorem localFromData_imp_localCheckBool (row : Row)
    {tab : Table} {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (cert : LocalPrecheckCertificate tab su sl) :
    row.localPreconditionCheckBoolFromData cert.data = true →
    row.localPreconditionCheckBool
      (LocalPrecheckAlg.ofOracle (LocalPrecheckCertificate.toOracle cert)) = true := by
  intro h
  -- Extract the eleven Bool atoms from the left-associated &&-chain
  simp only [Row.localPreconditionCheckBoolFromData, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩, h₉⟩, h₁₀⟩, h₁₁⟩ := h
  -- h₁ : nodeType = 2
  -- h₂ : localPoseInFourIntervalBool = true
  -- h₃ : localEpsPosBool = true
  -- h₄ : localRPosBool = true
  -- h₅..h₁₁ : oracleGet cert.data.X_ok row.ID = true  (for each of 7 checks)
  -- Build the right-associated &&-chain
  -- After unfolding, the alg fields reduce to oracleGet cert.data.X_ok row.ID
  unfold Row.localPreconditionCheckBool
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  -- The alg field accesses reduce definitionally:
  -- (ofOracle (toOracle cert)).boundR row = oracleGet cert.data.boundR_ok row.ID, etc.
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩

/-!
### Master bridge: leaf checks + split validity → Table.Precheck
-/

/-- Compose leaf-node checks and split-node validity into a full `Table.Precheck`.
This decouples the combinatorial dispatch from the specific check functions:
- `hleaf` provides the Bool check results for leaf nodes (type 1 and 2)
- `hsplit` provides `ValidSplit` for split nodes
- `hcover` ensures every row is one of the three types -/
theorem Table.Precheck_of_parts (tab : Table)
    (globalOk localOk congrOk : Row → Bool)
    (hleaf : ∀ i : Fin tab.size,
      (tab[i].nodeType = 1 → globalOk tab[i] = true) ∧
      (tab[i].nodeType = 2 → localOk tab[i] = true ∧ congrOk tab[i] = true))
    (hsplit : ∀ i : Fin tab.size,
      tab[i].nodeType ≠ 1 → tab[i].nodeType ≠ 2 → tab[i].ValidSplit tab)
    (hcover : ∀ i : Fin tab.size,
      tab[i].nodeType = 1 ∨ tab[i].nodeType = 2 ∨ tab[i].nodeType = 3) :
    Table.Precheck tab globalOk localOk congrOk := by
  intro i
  -- Dispatch on node type (from hcover)
  rcases hcover i with h1 | h2 | h3
  · -- Global leaf (nodeType = 1)
    exact Or.inl ⟨h1, (hleaf i).1 h1⟩
  · -- Local leaf (nodeType = 2)
    exact Or.inr (Or.inl ⟨h2, (hleaf i).2 h2⟩)
  · -- Split node (nodeType = 3)
    exact Or.inr (Or.inr (hsplit i (by omega) (by omega)))

end Solution
