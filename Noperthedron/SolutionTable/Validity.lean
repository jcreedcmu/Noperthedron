import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.LeafCertificates

namespace Solution

inductive Row.Valid (tab : Table) (row : Row) : Prop where
  | asSplit : row.ValidSplit tab → Row.Valid tab row
  | asGlobal : row.ValidGlobal tab → Row.Valid tab row
  | asLocal : row.ValidLocal tab → Row.Valid tab row
  | asGlobalRational : Row.ValidGlobalRational tab row → Row.Valid tab row
  | asLocalRational : Row.ValidLocalRational tab row → Row.Valid tab row

def Row.Valid.ofGlobalPrecheckBool (tab : Table) (row : Row)
    (alg : Solution.GlobalPrecheckAlg)
    (hpre : row.globalPreconditionCheckBool alg = true) :
    Row.Valid tab row :=
  Row.Valid.asGlobalRational
    (Row.ValidGlobalRational.ofPrecheckBool tab row alg hpre)

def Row.Valid.ofGlobalPrecheckBoolFromRowCerts (tab : Table) (row : Row)
    (certs : Solution.GlobalPrecheckRowCerts tab)
    (hpre : row.globalPreconditionCheckBoolFromRowCerts (tab := tab) certs = true) :
    Row.Valid tab row :=
  Row.Valid.asGlobalRational
    (Row.ValidGlobalRational.ofPrecheckBoolFromRowCerts tab row certs hpre)

def Row.Valid.ofLocalPrecheckBool (tab : Table) (row : Row)
    (hc : row.localCongruenceIndexCheck)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (alg : Solution.LocalPrecheckAlg su sl)
    (hpre : row.localPreconditionCheckBool alg = true) :
    Row.Valid tab row :=
  Row.Valid.asLocalRational
    (Row.ValidLocalRational.ofPrecheckBool tab row hc alg hpre)

def Row.Valid.ofLocalPrecheckBoolFromRowCerts (tab : Table) (row : Row)
    (hc : row.localCongruenceIndexCheck)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (certs : Solution.LocalPrecheckRowCerts tab su sl)
    (hpre : row.localPreconditionCheckBoolFromRowCerts (tab := tab) certs = true) :
    Row.Valid tab row :=
  Row.Valid.asLocalRational
    (Row.ValidLocalRational.ofPrecheckBoolFromRowCerts tab row hc certs hpre)

def Row.ValidIx (tab : Table) (i : ℕ) (row : Row) : Prop :=
  row.ID = i ∧ row.Valid tab ∧ row.ID < tab.size

def Table.Valid (tab : Table) : Prop :=
  ∀ i : Fin (tab.size), tab[i].ValidIx tab i

lemma Table.Valid.valid_at {tab : Table} (htab : tab.Valid) {i : ℕ} (hi : i < tab.size) :
    tab[i].ValidIx tab i :=
  htab ⟨i, hi⟩

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
    (global : Solution.GlobalPrecheckAlg)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (localAlg : Solution.LocalPrecheckAlg su sl)
    (congrOk : Bool)
    (hc_sound : congrOk = true → row.localCongruenceIndexCheck)
    (hpre : Row.ValidPrecheck tab row
      (row.globalPreconditionCheckBool global)
      (row.localPreconditionCheckBool localAlg)
      congrOk) :
    Row.Valid tab row := by
  rcases hpre with hglobal | hlocal | hsplit
  · rcases hglobal with ⟨hnode, hpre⟩
    have := Row.Valid.ofGlobalPrecheckBool tab row global hpre
    exact this
  · rcases hlocal with ⟨hnode, hpre, hcong⟩
    have hcong' : row.localCongruenceIndexCheck := hc_sound hcong
    have := Row.Valid.ofLocalPrecheckBool tab row hcong' localAlg hpre
    exact this
  · exact Row.Valid.asSplit hsplit

def Table.Valid.ofPrecheck (tab : Table)
    (hid : ∀ i : Fin tab.size, tab[i].ID = i)
    (global : Solution.GlobalPrecheckAlg)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (localAlg : Solution.LocalPrecheckAlg su sl)
    (congrOk : Row → Bool)
    (hc_sound : ∀ row, congrOk row = true → row.localCongruenceIndexCheck)
    (hpre : Table.Precheck tab
      (fun row => row.globalPreconditionCheckBool global)
      (fun row => row.localPreconditionCheckBool localAlg)
      congrOk) :
    Table.Valid tab := by
  intro i
  refine ⟨hid i, ?_, ?_⟩
  · have hrow := hpre i
    exact Row.Valid.ofPrecheck tab tab[i] global localAlg (congrOk tab[i]) (hc_sound tab[i]) hrow
  · have hi : (i : ℕ) < tab.size := i.isLt
    -- Avoid `simpa` rewriting the proof term itself (it sometimes reduces the type to `True` here).
    exact (hid i).symm ▸ hi

end Solution
