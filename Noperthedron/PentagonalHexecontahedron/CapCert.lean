module

public import Noperthedron.PentagonalHexecontahedron.CapCheck

@[expose] public section

/-!
# Cap certificates

`CapCert`: a cap (frame, parameters, the exact vertices, the witnesses) and
per chart of Lean's `chartList` its certificate tree. `CapCert.check` checks
(natively) that the charts are exactly `chartList`, that the frame is
orthonormal, and every tree; `CapCert.check_sound` gives `ChartGood` at every
point of every chart, hence (`cap_pose_not_rupert`) the cap theorem.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

structure CapCert where
  st : Setup
  pr : Params
  zList : List ((Kind × ℕ × ℕ × Bool) × ℕ)
  verts : Array KVec
  wits : Array (ℕ × KVec)
  usePrune : Bool
  Gcol : Fin 3 → KVec
  charts : List (ChartId × CTree)

def CapCert.zOf (c : CapCert) (b : Kind × ℕ × ℕ × Bool) : ℕ :=
  match c.zList.find? (fun e => decide (e.1 = b)) with
  | some e => e.2
  | none => 1

/-- Per used witness: the vertex, the direction, the screened polynomials and the d ≠ 0 check. -/
structure WitData where
  vk : KVec
  c : KVec
  Q : Array (NPoly 5)
  dok : Bool

def witData (c : CapCert) (id : ChartId) (wi : ℕ) : Option WitData :=
  match c.wits[wi]? with
  | some (k, cv) =>
    match c.verts[k]? with
    | some vk => some ⟨vk, cv, screened (witnessPolys (makeChart c.st id) id c.verts vk cv) (rootBox c.st c.pr id),
        dOk c.st c.pr id cv⟩
    | none => none
  | none => none

def leafCheck (c : CapCert) (id : ChartId) (cache : Array (Option WitData)) (wi : ℕ) (box : Box) : Bool :=
  match cache[wi]? with
  | some (some d) => d.dok && boxOk d.Q box
  | _ => false

def CTree.leafIds : CTree → List ℕ
  | .split _ l r => l.leafIds ++ r.leafIds
  | .leaf w => [w]
  | _ => []

def chartCheck (c : CapCert) (id : ChartId) (t : CTree) : Bool :=
  let root := rootBox c.st c.pr id
  let used := t.leafIds
  let cache : Array (Option WitData) :=
    (Array.range c.wits.size).map fun wi => if used.contains wi then witData c id wi else none
  decide (∀ i : Fin 5, 0 ≤ (root i).2) && decide (id.axis < 3) && decide (id.side < 4) &&
    t.check (leafCheck c id cache) (fun box => c.usePrune && pruneOk c.st id c.Gcol box) (coneOk c.st c.pr id) root

def frameCheck (st : Setup) : Bool :=
  decide (kdot st.e1 st.e1 = IcoQ.one) && decide (kdot st.e2 st.e2 = IcoQ.one) && decide (kdot st.x st.x = IcoQ.one) &&
  decide (kdot st.e1 st.e2 = IcoQ.zero) && decide (kdot st.e1 st.x = IcoQ.zero) && decide (kdot st.e2 st.x = IcoQ.zero)

/-- The tie scheme's parameters are admissible (`TieOK`). -/
def CapCert.tieCheck (c : CapCert) : Bool :=
  c.st.tieCharts.all fun e => (e.1.1 != .face) ||
    (decide (e.1.2.2.1 ≠ 0) && decide (c.zOf e.1 + e.2.1 ≤ e.2.2.1) && decide (e.2.2.1 < e.2.2.2) &&
      c.pr.ratioOn && c.st.strong e.1.2.2.1)

def CapCert.check (c : CapCert) : Bool :=
  decide (0 < c.verts.size) && c.zList.all (fun e => decide (0 < e.2)) && frameCheck c.st &&
    (c.charts.map (·.1) == chartList c.st c.pr c.zOf) && c.charts.all (fun e => chartCheck c e.1 e.2) &&
    c.tieCheck

theorem CapCert.tieOK (c : CapCert) (h : c.tieCheck = true) : TieOK c.st c.pr c.zOf := by
  intro b p hp hface
  unfold Setup.tieOf at hp
  obtain ⟨e, hfind, rfl⟩ := Option.map_eq_some_iff.mp hp
  have hmem := List.mem_of_find?_eq_some hfind
  have heq : e.1 = b := by simpa using List.find?_some hfind
  have he := List.all_eq_true.mp h e hmem
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at he
  rcases he with he | he
  · exact absurd (heq ▸ hface) he
  · rw [← heq]
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := he
    exact ⟨h1, h2, h3, h4, h5⟩

theorem frameCheck_sound (st : Setup) (h : frameCheck st = true) : FrameOK st := by
  simp only [frameCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h11, h22⟩, hxx⟩, h12⟩, h1x⟩, h2x⟩ := h
  have hv : ∀ a b : KVec, ∀ q : IcoQ, kdot a b = q → rdot (kv a) (kv b) = q.val := by
    intro a b q hq; rw [← val_kdot, hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv _ _ _ h11]; exact icoOne_val
  · rw [hv _ _ _ h22]; exact icoOne_val
  · rw [hv _ _ _ hxx]; exact icoOne_val
  · rw [hv _ _ _ h12]; simp [IcoQ.val, IcoQ.zero]
  · rw [hv _ _ _ h1x]; simp [IcoQ.val, IcoQ.zero]
  · rw [hv _ _ _ h2x]; simp [IcoQ.val, IcoQ.zero]

theorem CapCert.zOf_pos (c : CapCert) (h : c.zList.all (fun e => decide (0 < e.2)) = true) (b) : 0 < c.zOf b := by
  unfold CapCert.zOf
  split
  · next e he =>
    have hmem := List.mem_of_find?_eq_some he
    have := List.all_eq_true.mp h e hmem
    simpa using this
  · norm_num

theorem cache_spec (c : CapCert) (id : ChartId) (used : List ℕ) (wi : ℕ) (d : WitData)
    (h : ((Array.range c.wits.size).map fun wi => if used.contains wi then witData c id wi else none)[wi]? =
      some (some d)) : witData c id wi = some d := by
  rw [Array.getElem?_map, Array.getElem?_range] at h
  split_ifs at h with hwi
  · simp only [Option.map_some, Option.some.injEq] at h
    split_ifs at h with hu
    · exact h
  · simp at h

theorem witData_spec (c : CapCert) (id : ChartId) (wi : ℕ) (d : WitData) (h : witData c id wi = some d) :
    ∃ vk ∈ c.verts, ∃ cv : KVec, d = ⟨vk, cv,
      screened (witnessPolys (makeChart c.st id) id c.verts vk cv) (rootBox c.st c.pr id), dOk c.st c.pr id cv⟩ := by
  rcases hw : c.wits[wi]? with _ | ⟨k, cv⟩
  · simp only [witData, hw] at h; cases h
  · rcases hv : c.verts[k]? with _ | vk
    · simp only [witData, hw, hv] at h; cases h
    · simp only [witData, hw, hv, Option.some.injEq] at h
      exact ⟨vk, Array.mem_of_getElem? hv, cv, h.symm⟩

set_option maxHeartbeats 1000000 in
/-- **Certificate soundness**: a checked cap certificate makes every chart point good. -/
theorem CapCert.check_sound (c : CapCert) (h : c.check = true) :
    FrameOK c.st ∧ (∀ b, 0 < c.zOf b) ∧ TieOK c.st c.pr c.zOf ∧
      ∀ id ∈ chartList c.st c.pr c.zOf, ∀ y, InBoxR (rootBox c.st c.pr id) y →
        ChartGood c.st c.pr (c.verts.toList.map kv) c.usePrune (gMat c.Gcol) id y := by
  simp only [CapCert.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hV, hz⟩, hF⟩, hlist⟩, hall⟩, htc⟩ := h
  have hF' := frameCheck_sound c.st hF
  refine ⟨hF', c.zOf_pos hz, c.tieOK htc, ?_⟩
  intro id hid y hy
  rw [← hlist] at hid
  obtain ⟨⟨id', t⟩, hmem, rfl⟩ := List.mem_map.mp hid
  have hc := List.all_eq_true.mp hall _ hmem
  simp only [chartCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hw, hax⟩, hside⟩, htree⟩ := hc
  have hVne : c.verts.toList.map kv ≠ [] := by
    intro h0
    have : c.verts.toList = [] := List.map_eq_nil_iff.mp h0
    have : c.verts.size = 0 := by rw [← Array.length_toList, this]; rfl
    omega
  have hu := rChartU_ne_zero c.st hF' id' hside
  refine CTree.check_sound _ _ _ (fun y => InBoxR (rootBox c.st c.pr id') y →
      ChartGood c.st c.pr (c.verts.toList.map kv) c.usePrune (gMat c.Gcol) id' y)
    ?_ ?_ ?_ t (rootBox c.st c.pr id') hw htree y hy hy
  · -- Witness leaves.
    intro wi box hbw hleaf y hyb hyr
    unfold leafCheck at hleaf
    split at hleaf
    · next d hd =>
      obtain ⟨vk, hvk, cv, rfl⟩ := witData_spec c id' wi d (cache_spec c id' _ wi _ hd)
      have hok : witnessLeafOk c.st c.pr id' c.verts vk cv box = true := by
        unfold witnessLeafOk; simpa only using hleaf
      obtain ⟨hdn, hval⟩ := witnessLeafOk_sound c.st c.pr id' hax c.verts vk cv box hok hw hbw y hyb hyr
      right; right
      refine ⟨kv vk, List.mem_map.mpr ⟨vk, Array.mem_toList_iff.mpr hvk, rfl⟩, kv cv, hdn, ?_⟩
      intro vj' hvj'
      obtain ⟨vj, hvj, rfl⟩ := List.mem_map.mp hvj'
      exact hval vj (Array.mem_toList_iff.mp hvj)
    · exact absurd hleaf (by simp)
  · -- Half-turn prune leaves.
    intro box hbw hprune y hyb hyr
    simp only [Bool.and_eq_true] at hprune
    obtain ⟨hpr, hok⟩ := hprune
    have hμ0 := y0_nonneg_of_root c.st c.pr id' y hyr
    rcases eq_or_lt_of_le hμ0 with h0 | hpos
    · exact chartGood_of_w_zero _ _ _ hVne _ _ _ _ (hu y) (rChartW_mu_zero c.st id' y h0.symm)
    · have hnm : id'.kind ≠ .mcone := by
        simp only [pruneOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
      by_cases hcone : isCone id' = true
      · have hk : id'.kind = .cone := by
          unfold isCone at hcone; simp at hcone
          rcases hcone with h | h
          · exact h
          · exact absurd h hnm
        have h2 := y2_nonneg_of_root_cone c.st c.pr id' hcone hax y hyr
        rcases eq_or_lt_of_le h2 with h20 | h2pos
        · exact chartGood_of_w_zero _ _ _ hVne _ _ _ _ (hu y) (rChartW_cone_tip c.st id' hk y h20.symm)
        · right; left
          exact ⟨hpr, pruneOk_sound c.st id' c.Gcol box hok hbw y hyb hpos (fun _ => h2pos)
            (rdot_self_ne_zero_of_ne (hu y))⟩
      · right; left
        exact ⟨hpr, pruneOk_sound c.st id' c.Gcol box hok hbw y hyb hpos (fun h => absurd h hcone)
          (rdot_self_ne_zero_of_ne (hu y))⟩
  · -- Cone-region leaves.
    intro box hbw hcone y hyb hyr
    left
    exact coneOk_sound c.st c.pr id' box hcone y hyb

open scoped Matrix in
/-- **The cap theorem from a checked certificate.** -/
theorem CapCert.not_rupert (c : CapCert) (hc : c.check = true) (hS : 2 ≤ c.st.strongScale)
    (hmcm : 1 ≤ c.st.mcm) (ht0 : 0 ≤ (c.pr.t0 : ℝ)) (ht0m : 0 ≤ (c.pr.t0m : ℝ)) (wmax : ℝ) (hw0 : 0 ≤ wmax) (hw1 : wmax ≤ 2 * c.pr.mu0)
    (hw2 : wmax ≤ c.st.strongScale * (c.pr.mu0 : ℝ) ^ 2)
    (κ : ℝ) (hκ : 0 < κ) (S : Set ℝ³) (hSdef : S = convexHull ℝ {v | ∃ vj ∈ c.verts.toList.map kv, v = κ • toEuc vj})
    (hSsym : ∀ v ∈ S, -v ∈ S) (p : MatrixPose)
    (hx : 0 < rdot p.view (kv c.st.x))
    (he1 : |rdot p.view (kv c.st.e1)| ≤ c.pr.mu0 * rdot p.view (kv c.st.x))
    (he2 : |rdot p.view (kv c.st.e2)| ≤ c.pr.mu0 * rdot p.view (kv c.st.x))
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2)) (hw : rdot w w ≤ wmax ^ 2)
    (hcell : c.usePrune = true →
      Matrix.trace (halfTurnMat p.view * p.relativeRotation * gMat c.Gcol) ≤ Matrix.trace p.relativeRotation) :
    ¬ RupertPose p S := by
  obtain ⟨hF, hz, htie, hgood⟩ := c.check_sound hc
  exact cap_pose_not_rupert c.st c.pr c.zOf hz htie hF hS hmcm ht0 ht0m wmax hw0 hw1 hw2 _ c.usePrune (gMat c.Gcol) hgood κ hκ S
    hSdef hSsym p hx he1 he2 w hR hw hcell

end Noperthedron.PentagonalHexecontahedron.Cap
