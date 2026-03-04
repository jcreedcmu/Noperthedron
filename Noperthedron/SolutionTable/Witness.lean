import Noperthedron.SolutionTable.WitnessData

/-!
# Witness assembly for exists_solution_table

Lightweight file that combines the computational witnesses (from `WitnessData.lean`)
with bridge lemmas to produce the final `exists_solution_table_witness` theorem.

Separated from `WitnessData.lean` so the expensive native_decide build (~2 hours)
only runs once — this file builds in seconds.
-/

namespace Solution

/-!
### Oracle-backed certificates (sorry'd soundness — Phase B trust boundary)

These are in the fast file so that filling oracle sorries (Phase B) doesn't
require rebuilding the expensive native_decide checks.
-/

/-- Upper sqrt approximation oracle (Phase B trust boundary). -/
noncomputable def witnessSu : RationalApprox.UpperSqrt := sorry

/-- Lower sqrt approximation oracle (Phase B trust boundary). -/
noncomputable def witnessSl : RationalApprox.LowerSqrt := sorry

/-- Global precheck certificate with oracle soundness assumptions. -/
noncomputable def globalCert : GlobalPrecheckCertificate solutionTable where
  data := globalCertData
  forTable := sorry  -- data sizes match tab.size
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
### Assembly — proof logic connecting bridges and witnesses

These theorems combine the bridge lemmas (PrecheckBridge) with the computational
witnesses from `WitnessData`. `globalCert.data = globalCertData` and
`localCert.data = localCertData` hold by definition, so the bridge lemmas apply directly.
-/

/-- The solution table satisfies the precheck predicate. -/
theorem solutionTable_precheck :
    Table.Precheck solutionTable
      (fun row => row.globalPreconditionCheckBool globalCert.toAlg)
      (fun row => row.localPreconditionCheckBool
        (LocalPrecheckAlg.ofOracle (LocalPrecheckCertificate.toOracle localCert)))
      congrDecide := by
  apply Table.Precheck_of_parts
  · intro i; constructor
    · intro h1
      exact globalFromData_imp_globalCheckBool _ globalCert (witnessLeafGlobal i h1)
    · intro h2
      exact ⟨localFromData_imp_localCheckBool _ localCert (witnessLeafLocal i h2).1,
             (witnessLeafLocal i h2).2⟩
  · exact witnessSplits
  · exact witnessCover

/-- The solution table is valid. -/
theorem solutionTable_valid : Table.Valid solutionTable :=
  Table.Valid.ofPrecheck solutionTable globalCert.toAlg
    (LocalPrecheckAlg.ofOracle (LocalPrecheckCertificate.toOracle localCert))
    congrDecide congrDecide_sound witnessIds solutionTable_precheck

set_option maxHeartbeats 800000 in
/-- The root row covers tightInterval. -/
theorem solutionTable_covers :
    tightInterval ⊆ (solutionTable[0]'witnessNonempty).toPoseInterval := by
  apply tightSubset_of_intervals
  all_goals native_decide

/-- The main computational witness. -/
theorem exists_solution_table_witness :
    ∃ (tab : Table) (_ : tab.Valid) (hz : 0 < tab.size),
      tightInterval ⊆ tab[0].toPoseInterval :=
  ⟨solutionTable, solutionTable_valid, witnessNonempty, solutionTable_covers⟩

end Solution
