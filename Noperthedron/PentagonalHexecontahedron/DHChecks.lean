module

public import Noperthedron.PentagonalHexecontahedron.DHTies
public import Noperthedron.ParallelBool

@[expose] public section

/-!
# Parallel forms of the deltoidal hexecontahedron's cap and tie checks

`CapCert.checkPar` and `tiesCheckPar` evaluate the per-chart and per-node
checks as native tasks (`ParallelBool.allParB`); `check_of_par` and
`tiesCheck_of_par` recover the sequential checks, so the executable's
parallel run proves the same statements.
-/

namespace Noperthedron.PentagonalHexecontahedron.DH

open Cap Tie

def chartPred (c : CapCert) (i : ℕ) : Bool :=
  match c.charts[i]? with
  | some e => chartCheck c e.1 e.2
  | none => true

/-- `CapCert.check` with the chart trees checked in parallel. -/
def capCheckPar (c : CapCert) : Bool :=
  decide (0 < c.verts.size) && c.zList.all (fun e => decide (0 < e.2)) && Cap.frameCheck c.st &&
    (c.charts.map (·.1) == chartList c.st c.pr c.zOf) &&
    ParallelBool.allParB (chartPred c) c.charts.length c.charts.length && c.tieCheck

theorem check_of_par (c : CapCert) (h : capCheckPar c = true) : c.check = true := by
  simp only [capCheckPar, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hV, hz⟩, hF⟩, hlist⟩, hpar⟩, htc⟩ := h
  have hall := ParallelBool.all_of_parB hpar
  simp only [CapCert.check, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hV, hz⟩, hF⟩, hlist⟩, ?_⟩, htc⟩
  rw [List.all_eq_true]
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have := hall i hi
  simpa [chartPred, List.getElem?_eq_getElem hi] using this

def certForBasePar (c : CapCert) (b : CapBase) : Bool :=
  capCheckPar c && decide (2 ≤ c.st.strongScale) && decide (1 ≤ c.st.mcm) && decide (0 ≤ c.pr.t0) &&
    decide (0 ≤ c.pr.t0m) && keq c.st.x b.x && keq c.st.e1 b.e1 && keq c.st.e2 b.e2 &&
    decide (c.pr.mu0 = b.mu0) && decide (0 ≤ b.mu0) && decide (0 ≤ b.wmax2) && decide (b.wmax2 ≤ 3) &&
    decide (b.wmax2 ≤ 4 * b.mu0 ^ 2) && decide (b.wmax2 ≤ (c.st.strongScale : ℚ) ^ 2 * b.mu0 ^ 4) &&
    sameSlots c.verts.toList && pruneOk c b

theorem certForBase_of_par (c : CapCert) (b : CapBase) (h : certForBasePar c b = true) : certForBase c b = true := by
  unfold certForBasePar at h
  unfold certForBase
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨check_of_par c hc, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩

def capsCheckPar (certs : Array CapCert) : Bool :=
  (List.range dhCapBases.size).all fun k =>
    match dhCapBases[k]?, certs[k]? with
    | some b, some c => certForBasePar c b
    | _, _ => false

theorem capsCheck_of_par (certs : Array CapCert) (h : capsCheckPar certs = true) : capsCheck certs = true := by
  simp only [capsCheckPar, capsCheck, List.all_eq_true] at h ⊢
  intro k hk
  have := h k hk
  split at this
  · rename_i b c hb hc
    rw [hb, hc]
    exact certForBase_of_par c b this
  · simp at this

/-- `tiesCheck` with the tie nodes checked in parallel. -/
def tiesCheckPar (C : TieCerts) : Bool :=
  sameSlots C.V.toList && ParallelBool.allParB (nodePred C) dhTieNodes.size dhTieNodes.size

theorem tiesCheck_of_par (C : TieCerts) (h : tiesCheckPar C = true) : tiesCheck C = true := by
  unfold tiesCheckPar at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hs, hpar⟩ := h
  have hall := ParallelBool.all_of_parB hpar
  unfold tiesCheck
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨hs, fun k hk => hall k (List.mem_range.mp hk)⟩

end Noperthedron.PentagonalHexecontahedron.DH
