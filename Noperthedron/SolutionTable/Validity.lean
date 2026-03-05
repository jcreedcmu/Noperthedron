import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.LeafCertificates
import Noperthedron.SolutionTable.RationalGlobalCheck
import Noperthedron.SolutionTable.RationalLocalCheck.Computable.Oracle

namespace Solution

inductive Row.Valid (tab : Table) (row : Row) : Prop where
  | asSplit : row.ValidSplit tab → Row.Valid tab row
  | asGlobal : row.ValidGlobal tab → Row.Valid tab row
  | asLocal : row.ValidLocal tab → Row.Valid tab row
  | asGlobalRational : Row.ValidGlobalRational tab row → Row.Valid tab row
  | asLocalRational : Row.ValidLocalRational tab row → Row.Valid tab row

def Row.ValidIx (tab : Table) (i : ℕ) (row : Row) : Prop :=
  row.ID = i ∧ row.Valid tab ∧ row.ID < tab.size

def Table.Valid (tab : Table) : Prop :=
  ∀ i : Fin (tab.size), tab[i].ValidIx tab i

lemma Table.Valid.valid_at {tab : Table} (htab : tab.Valid) {i : ℕ} (hi : i < tab.size) :
    tab[i].ValidIx tab i :=
  htab ⟨i, hi⟩

noncomputable def Row.Valid.ofGlobalPrecheckBool (tab : Table) (row : Row)
    (alg : Solution.GlobalPrecheckAlg)
    (hpre : row.globalPreconditionCheckBool alg = true) :
    Row.Valid tab row :=
  Row.Valid.asGlobalRational
    (Row.ValidGlobalRational.ofPrecheckBool tab row alg hpre)

noncomputable def Row.Valid.ofLocalPrecheckBool (tab : Table) (row : Row)
    (hc : row.localCongruenceIndexCheck)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (alg : Solution.LocalPrecheckAlg su sl)
    (hpre : row.localPreconditionCheckBool alg = true) :
    Row.Valid tab row :=
  Row.Valid.asLocalRational
    (Row.ValidLocalRational.ofPrecheckBool tab row hc alg hpre)

def Row.ValidPrecheck (tab : Table) (row : Row)
    (globalOk localOk congrOk : Bool) : Prop :=
  row.nodeType = 1 ∧ globalOk = true ∨
  row.nodeType = 2 ∧ localOk = true ∧ congrOk = true ∨
  row.ValidSplit tab

def Table.Precheck (tab : Table)
    (globalOk localOk congrOk : Row → Bool) : Prop :=
  ∀ i : Fin tab.size,
    Row.ValidPrecheck tab tab[i] (globalOk tab[i]) (localOk tab[i]) (congrOk tab[i])

lemma Row.Valid.ofPrecheck (tab : Table) (row : Row)
    (globalAlg : Solution.GlobalPrecheckAlg)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (localAlg : Solution.LocalPrecheckAlg su sl)
    (congrOk : Bool)
    (hc_sound : congrOk = true → row.localCongruenceIndexCheck)
    (hpre : Row.ValidPrecheck tab row
      (row.globalPreconditionCheckBool globalAlg)
      (row.localPreconditionCheckBool localAlg)
      congrOk) :
    Row.Valid tab row := by
  rcases hpre with hglobal | hlocal | hsplit
  · exact Row.Valid.ofGlobalPrecheckBool tab row globalAlg hglobal.2
  · rcases hlocal with ⟨_, hpre, hcong⟩
    exact Row.Valid.ofLocalPrecheckBool tab row (hc_sound hcong) localAlg hpre
  · exact Row.Valid.asSplit hsplit

theorem Table.Valid.ofPrecheck (tab : Table)
    (globalAlg : Solution.GlobalPrecheckAlg)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (localAlg : Solution.LocalPrecheckAlg su sl)
    (congrOk : Row → Bool)
    (hc_sound : ∀ row, congrOk row = true → row.localCongruenceIndexCheck)
    (hids : ∀ i : Fin tab.size, tab[i].ID = i)
    (hpre : Table.Precheck tab
      (fun row => row.globalPreconditionCheckBool globalAlg)
      (fun row => row.localPreconditionCheckBool localAlg)
      congrOk) :
    Table.Valid tab := by
  intro i
  refine ⟨hids i, ?_, ?_⟩
  · exact Row.Valid.ofPrecheck tab tab[i] globalAlg localAlg (congrOk tab[i]) (hc_sound tab[i])
      (hpre i)
  · rw [hids i]; exact i.isLt

end Solution
