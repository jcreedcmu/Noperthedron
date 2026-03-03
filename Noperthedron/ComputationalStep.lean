import Noperthedron.PoseInterval
import Noperthedron.Nopert
import Noperthedron.SolutionTable
import Noperthedron.SolutionTable.Witness

structure SolutionTablePrecheckData where
  localData : Solution.LocalPrecheckCertificateData
  globalData : Solution.GlobalPrecheckCertificateData

def solutionTablePrecheckBool (tab : Solution.Table)
    (data : SolutionTablePrecheckData) : Bool :=
  Solution.Table.precheckBoolFromData tab data.localData data.globalData

def solutionTablePrecheckBoolWithCongruence (tab : Solution.Table)
    (data : SolutionTablePrecheckData) (congruence : Array Bool) : Bool :=
  Solution.Table.precheckBoolFromDataWithCongruence tab data.localData data.globalData congruence

def solutionTableValidFromPrecheck (tab : Solution.Table)
    (hid : ∀ i : Fin tab.size, tab[i].ID = i)
    (global : Solution.GlobalPrecheckAlg)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (localAlg : Solution.LocalPrecheckAlg su sl)
    (congrOk : Solution.Row → Bool)
    (hc_sound : ∀ row, congrOk row = true → row.localCongruenceIndexCheck)
    (hpre : Solution.Table.Precheck tab
      (fun row => row.globalPreconditionCheckBool global)
      (fun row => row.localPreconditionCheckBool localAlg)
      congrOk) :
    Solution.Table.Valid tab :=
  Solution.Table.Valid.ofPrecheck tab hid global localAlg congrOk hc_sound hpre

theorem exists_solution_table :
    ∃ (tab : Solution.Table) (tab_valid : tab.Valid)
      (hz : 0 < tab.size),
      tightInterval ⊆ tab[0].toPoseInterval :=
  Solution.exists_solution_table_witness

theorem exists_solution_table_of_precheck
    (tab : Solution.Table)
    (hid : ∀ i : Fin tab.size, tab[i].ID = i)
    (global : Solution.GlobalPrecheckAlg)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (localAlg : Solution.LocalPrecheckAlg su sl)
    (congrOk : Solution.Row → Bool)
    (hc_sound : ∀ row, congrOk row = true → row.localCongruenceIndexCheck)
    (hpre : Solution.Table.Precheck tab
      (fun row => row.globalPreconditionCheckBool global)
      (fun row => row.localPreconditionCheckBool localAlg)
      congrOk)
    (hz : 0 < tab.size)
    (hsubset : tightInterval ⊆ tab[0].toPoseInterval) :
    ∃ (tab_valid : tab.Valid), (0 < tab.size) ∧ tightInterval ⊆ tab[0].toPoseInterval := by
  refine ⟨solutionTableValidFromPrecheck tab hid global localAlg congrOk hc_sound hpre, hz, hsubset⟩
