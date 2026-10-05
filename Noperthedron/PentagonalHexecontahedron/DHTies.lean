module

public import Noperthedron.PentagonalHexecontahedron.DHCaps
public import Noperthedron.PentagonalHexecontahedron.TieRow

@[expose] public section

/-!
# The tie claims for the exact deltoidal hexecontahedron

`tiesHold_of_certs`: given the tie data (the solid's vertices, per pinning
normal its L = σ_x K and witness candidates) and a certificate per leaf tie
node (`TieCerts`, decoded from nopert229's `tietube.cc --export`) that pass
`tiesCheck`, every tie node of `dhTieNodes` has its claim for `dhIModel`'s hull
(`TiesHold`): leaves by `tie_claim`, split nodes from their four children
(`mem_split`). The certificates are checked natively.
-/

namespace Noperthedron.PentagonalHexecontahedron.DH

open NPoly PVec Cap Tie
open Noperthedron.Atlas.ProjectiveView (InTriangle toReal mem_split)

structure TieCerts where
  V : Array KVec
  normals : Array TieNormal
  /-- Per tie node, its six face trees (leaves; empty for split nodes). -/
  leaves : Array (List CTree)

/-- One tie node: a leaf has a checked certificate for its normal; a split node has four later
children, the midpoint split of its triangle, with the same normal and radii at least its own. -/
def nodeOk (C : TieCerts) (k : ℕ) (e : TieNode) : Bool :=
  match e.kids with
  | [] =>
    match C.normals[e.normal]?, C.leaves[k]? with
    | some N, some trees => keq N.x (AtlasTiePrune.tieXK e.normal) && lCheck N C.V &&
        tieCertCheck N C.V e.tri e.rho trees
    | _, _ => false
  | [a, b, c, d] => decide (0 ≤ e.rho) && (List.finRange 4).all fun i =>
      let kid := (![a, b, c, d] : Fin 4 → ℕ) i
      decide (k < kid) &&
      match dhTieNodes[kid]? with
      | some f => decide (f.normal = e.normal) && decide (f.tri = Noperthedron.Atlas.ProjectiveView.split e.tri i) &&
          decide (e.rho ≤ f.rho)
      | none => false
  | _ => false

def tiesCheck (C : TieCerts) : Bool :=
  sameSlots C.V.toList && (List.range dhTieNodes.size).all fun k =>
    match dhTieNodes[k]? with
    | some e => nodeOk C k e
    | none => false

theorem tieClaimT_mono {S : Set ℝ³} {x : Fin 3 → ℝ} {T : Triangle} {ρ ρ' : ℚ} (h : TieClaimT S x T ρ)
    (h0 : 0 ≤ ρ') (hle : ρ' ≤ ρ) : TieClaimT S x T ρ' := by
  intro p κ pt hκ hin hv htr
  apply h p κ pt hκ hin hv (le_trans ?_ htr)
  exact_mod_cast tau_anti h0 hle

theorem node_claim (C : TieCerts) (h : tiesCheck C = true) :
    ∀ m k, dhTieNodes.size - k ≤ m → ∀ e, dhTieNodes[k]? = some e →
      TieClaimT dhIModel.toC5.polyhedron.hull (kv (AtlasTiePrune.tieXK e.normal)) e.tri e.rho := by
  simp only [tiesCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hslots, hnodes⟩ := h
  intro m
  induction m with
  | zero =>
    intro k hk e he
    have : k < dhTieNodes.size := (Array.getElem?_eq_some_iff.mp he).1
    omega
  | succ m ih =>
    intro k hk e he
    have hk' : k < dhTieNodes.size := (Array.getElem?_eq_some_iff.mp he).1
    have hok := hnodes k hk'
    rw [he] at hok
    simp only at hok
    unfold nodeOk at hok
    split at hok
    · -- A leaf: its certificate.
      split at hok
      · rename_i N trees hN htrees
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨hx, hL⟩, hc⟩ := hok
        have hclaim := tie_claim N C.V e.tri e.rho trees hL hc (dhScale : ℝ) dhScale_pos _
          (dhHull_eq _ hslots) dhIModel_centrallySymmetric
        rw [eq_of_keq hx] at hclaim
        exact tieClaimT_of_tieClaim hclaim
      · simp at hok
    · -- A split node: its children.
      rename_i a b c d hkids
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const] at hok
      obtain ⟨hρ0, hkid⟩ := hok
      intro p κ pt hκ hin hv htr
      obtain ⟨i, hi⟩ := mem_split hin
      obtain ⟨hlt, hf⟩ := hkid i
      split at hf
      · rename_i f hfe
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
        obtain ⟨⟨hn, htri⟩, hρ⟩ := hf
        have hfc := ih _ (by omega) f hfe
        rw [hn, htri] at hfc
        exact tieClaimT_mono hfc hρ0 hρ p κ pt hκ hi hv htr
      · simp at hf
    · exact absurd hok (by decide)

/-- **The tie claims hold** for the exact solid, given checked tie certificates. -/
theorem tiesHold_of_certs (C : TieCerts) (h : tiesCheck C = true) : TiesHold dhIModel.toC5.polyhedron.hull :=
  fun k e he => node_claim C h _ k le_rfl e he

/-- **The deltoidal hexecontahedron is not Rupert**, given the checked solution tables (which
exclude every centrally symmetric `IModel` whose exact claims hold), checked cap certificates and
checked tie certificates. -/
theorem deltoidalHexecontahedron_not_rupert_of_checks
    (htables : ∀ P : IModel, P.CentrallySymmetric →
      AtlasProjectiveSolutionTree.ExactClaims P.toC5.polyhedron.hull → ¬ IsRupert P.toC5.verts)
    (caps : Array CapCert) (hcaps : capsCheck caps = true)
    (ties : TieCerts) (hties : tiesCheck ties = true) :
    ∀ V : Finset ℝ³, IsDeltoidalHexecontahedron V → ¬ IsRupert V :=
  deltoidalHexecontahedron_not_rupert
    (htables dhIModel dhIModel_centrallySymmetric ⟨capsHold_of_certs caps hcaps, tiesHold_of_certs ties hties⟩)

end Noperthedron.PentagonalHexecontahedron.DH
