import Noperthedron.SolutionTable.WitnessData
import Noperthedron.RationalApprox.NewtonSqrt

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

/-- Upper sqrt approximation via Newton iteration. -/
noncomputable def witnessSu : RationalApprox.UpperSqrt := RationalApprox.newtonUpperSqrt

/-- Lower sqrt approximation via Newton iteration. -/
noncomputable def witnessSl : RationalApprox.LowerSqrt := RationalApprox.newtonLowerSqrt

/-- S array: maps each row's S_index to the corresponding noperthedron vertex. -/
noncomputable def witnessS : Array ℝ³ :=
  Array.ofFn fun (i : Fin solutionTable.size) =>
    Row.indexPoint (solutionTable[i].S_index)

/-- Global certificate data with proper S array populated from witness data. -/
noncomputable def globalCertDataWithS : GlobalPrecheckCertificateData :=
  { S := witnessS, exceeds_ok := exceedsOkData }

/-- `globalPreconditionCheckBoolFromData` only depends on the `exceeds_ok` field. -/
private theorem globalFromData_exceeds_only (row : Row)
    (d1 d2 : GlobalPrecheckCertificateData)
    (h : d1.exceeds_ok = d2.exceeds_ok) :
    row.globalPreconditionCheckBoolFromData d1 =
    row.globalPreconditionCheckBoolFromData d2 := by
  simp [Row.globalPreconditionCheckBoolFromData, h]

/-- Global precheck certificate with oracle soundness assumptions. -/
noncomputable def globalCert : GlobalPrecheckCertificate solutionTable where
  data := globalCertDataWithS
  forTable := { S := by unfold globalCertDataWithS witnessS; exact Array.size_ofFn
                exceeds := rfl }
  S_in_poly := fun _row h => by
    unfold globalCertDataWithS witnessS
    dsimp only []
    show (Array.ofFn fun i => Row.indexPoint (solutionTable[i].S_index))[_row.ID] ∈ _
    rw [Array.getElem_ofFn]
    exact Row.indexPoint_mem_nopertVerts _
  exceeds_sound := sorry -- oracle trust: external verifier validated Gℚ > maxHℚ

/-- Local precheck certificate with oracle soundness assumptions. -/
noncomputable def localCert :
    LocalPrecheckCertificate solutionTable witnessSu witnessSl where
  data := localCertData
  forTable := { boundR := rfl, boundDelta := rfl, ae1 := rfl,
                ae2 := rfl, span1 := rfl, span2 := rfl, be := rfl }
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
      -- witnessLeafGlobal gives us `...FromData globalCertData = true`
      -- but globalCert.data = globalCertDataWithS, so we bridge via exceeds_only
      have hFromData := witnessLeafGlobal i h1
      have hBridge := globalFromData_exceeds_only (solutionTable[i]) globalCertData
        globalCertDataWithS rfl
      exact globalFromData_imp_globalCheckBool _ globalCert (hBridge ▸ hFromData)
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
