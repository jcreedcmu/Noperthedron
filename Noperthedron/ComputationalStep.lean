import Noperthedron.PoseInterval
import Noperthedron.Nopert
import Noperthedron.SolutionTable

noncomputable def solutionTableValidFromPrecheck (tab : Solution.Table)
    (globalAlg : Solution.GlobalPrecheckAlg)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (localAlg : Solution.LocalPrecheckAlg su sl)
    (congrOk : Solution.Row → Bool)
    (hc_sound : ∀ row, congrOk row = true → row.localCongruenceIndexCheck)
    (hids : ∀ i : Fin tab.size, tab[i].ID = i)
    (hpre : Solution.Table.Precheck tab
      (fun row => row.globalPreconditionCheckBool globalAlg)
      (fun row => row.localPreconditionCheckBool localAlg)
      congrOk) :
    Solution.Table.Valid tab :=
  Solution.Table.Valid.ofPrecheck tab globalAlg localAlg congrOk hc_sound hids hpre

theorem exists_solution_table :
    ∃ (tab : Solution.Table) (tab_valid : tab.Valid)
      (hz : 0 < tab.size),
      tightInterval ⊆ tab[0].toPoseInterval
     := by
  sorry -- Filled by Witness.lean assembly
