import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.LeafCertificates

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

end Solution

