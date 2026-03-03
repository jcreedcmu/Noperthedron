import Noperthedron.SolutionTable.PrecheckBridge
import Noperthedron.SolutionTable.TightSubset

/-!
# Witness module for exists_solution_table

This module assembles all components needed to fill the `exists_solution_table` sorry.
The proof structure is complete — the only `sorry`s are in:
1. **Data definitions** (`solutionTable`, certificate data) — will be replaced by loaded data
2. **Computational witnesses** (native_decide proofs) — will compile once data is loaded
3. **Oracle soundness fields** in certificates — the trust boundary for Phase B

When the data pipeline is ready, replace sorry'd definitions with:
- `solutionTable` ← loaded from binary/parquet
- native_decide witnesses ← compile with `native_decide`
- Oracle soundness ← Phase B (computable Gℚ/maxHℚ, sqrt approximations)
-/

namespace Solution

/-!
### Data definitions (sorry'd — awaiting data pipeline)
-/

/-- The 18.7M-row solution table. Will be loaded from binary data at elaboration time. -/
def solutionTable : Table := sorry

/-- Global certificate data: per-row S vertex and exceeds_ok arrays. -/
noncomputable def globalCertData : GlobalPrecheckCertificateData := sorry

/-- Local certificate data: per-row Bool arrays for the 7 oracle checks. -/
def localCertData : LocalPrecheckCertificateData := sorry

/-- Upper sqrt approximation oracle. -/
noncomputable def witnessSu : RationalApprox.UpperSqrt := sorry

/-- Lower sqrt approximation oracle. -/
noncomputable def witnessSl : RationalApprox.LowerSqrt := sorry

/-!
### Oracle-backed certificates (sorry'd soundness — Phase B trust boundary)
-/

/-- Global precheck certificate with oracle soundness assumptions. -/
noncomputable def globalCert : GlobalPrecheckCertificate solutionTable where
  data := globalCertData
  forTable := sorry  -- data.S.size = tab.size, data.exceeds_ok.size = tab.size
  S_in_poly := sorry -- oracle trust: external verifier validated S ∈ vertices
  exceeds_sound := sorry -- oracle trust: external verifier validated Gℚ > maxHℚ

/-- Local precheck certificate with oracle soundness assumptions. -/
noncomputable def localCert :
    LocalPrecheckCertificate solutionTable witnessSu witnessSl where
  data := localCertData
  forTable := sorry -- 7 size equalities
  boundR_sound := sorry -- oracle trust
  boundDelta_sound := sorry -- oracle trust
  ae1_sound := sorry -- oracle trust
  ae2_sound := sorry -- oracle trust
  span1_sound := sorry -- oracle trust
  span2_sound := sorry -- oracle trust
  be_sound := sorry -- oracle trust

/-!
### Computational witnesses (sorry'd — will be `native_decide` once data loaded)
-/

/-- Every row's ID matches its array index. -/
theorem witnessIds :
    ∀ i : Fin solutionTable.size, solutionTable[i].ID = i := sorry

/-- Split rows have valid split structure (integer arithmetic on child intervals). -/
theorem witnessSplits :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType ≠ 1 → solutionTable[i].nodeType ≠ 2 →
      solutionTable[i].ValidSplit solutionTable := sorry

/-- Global leaf rows pass the FromData global check. -/
theorem witnessLeafGlobal :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType = 1 →
      solutionTable[i].globalPreconditionCheckBoolFromData globalCert.data = true := sorry

/-- Local leaf rows pass the FromData local check and congruence check. -/
theorem witnessLeafLocal :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType = 2 →
      solutionTable[i].localPreconditionCheckBoolFromData localCert.data = true ∧
      congrDecide solutionTable[i] = true := sorry

/-- Every row is a global leaf, local leaf, or split node. -/
theorem witnessCover :
    ∀ i : Fin solutionTable.size,
      solutionTable[i].nodeType = 1 ∨
      solutionTable[i].nodeType = 2 ∨
      solutionTable[i].nodeType = 3 := sorry

/-- The table is non-empty. -/
theorem witnessNonempty : 0 < solutionTable.size := sorry

/-!
### Assembly — no sorry in proof logic

These theorems combine the bridge lemmas (PrecheckBridge) with the computational
witnesses above. The proof structure is fully verified; only data is sorry'd.
-/

/-- The solution table satisfies the precheck predicate. -/
theorem solutionTable_precheck :
    Table.Precheck solutionTable
      (fun row => row.globalPreconditionCheckBool globalCert.toAlg)
      (fun row => row.localPreconditionCheckBool
        (LocalPrecheckAlg.ofOracle (LocalPrecheckCertificate.toOracle localCert)))
      congrDecide := by
  apply Table.Precheck_of_parts
  · -- hleaf: bridge FromData checks to alg-based checks
    intro i; constructor
    · intro h1
      exact globalFromData_imp_globalCheckBool _ globalCert (witnessLeafGlobal i h1)
    · intro h2
      exact ⟨localFromData_imp_localCheckBool _ localCert (witnessLeafLocal i h2).1,
             (witnessLeafLocal i h2).2⟩
  · -- hsplit: direct from witnessSplits
    exact witnessSplits
  · -- hcover: direct from witnessCover
    exact witnessCover

/-- The solution table is valid. -/
theorem solutionTable_valid : Table.Valid solutionTable :=
  Table.Valid.ofPrecheck solutionTable globalCert.toAlg
    (LocalPrecheckAlg.ofOracle (LocalPrecheckCertificate.toOracle localCert))
    congrDecide congrDecide_sound witnessIds solutionTable_precheck

/-- The main computational witness: there exists a valid solution table covering tightInterval.

The `sorry` in the tightInterval coverage step will be replaced by `tightSubset_of_intervals`
applied to concrete row-0 bounds once the data pipeline provides `solutionTable`. -/
theorem exists_solution_table_witness :
    ∃ (tab : Table) (_ : tab.Valid) (hz : 0 < tab.size),
      tightInterval ⊆ tab[0].toPoseInterval := by
  refine ⟨solutionTable, solutionTable_valid, witnessNonempty, ?_⟩
  -- Goal: tightInterval ⊆ solutionTable[0].toPoseInterval
  -- Once data is loaded, apply tightSubset_of_intervals with native_decide'd bounds.
  -- For now, sorry'd because solutionTable[0] requires concrete data.
  sorry

end Solution
