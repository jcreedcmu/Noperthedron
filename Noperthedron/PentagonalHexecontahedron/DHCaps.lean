module

public import Noperthedron.PentagonalHexecontahedron.DHStatement
public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveSolutionTree

@[expose] public section

/-!
# The cap claims for the exact deltoidal hexecontahedron

`capsHold_of_certs`: given one cap certificate per base cap (`dhCapBases`)
that passes `certForBase` (its check, its frame, μ₀ and half-turn element
equal to the base's, its |w|² bound admissible, and its vertex list the exact
solid's slots), every cap image's claim holds for `dhIModel`'s hull
(`CapsHold`). The certificates are decoded and checked natively.
-/

namespace Noperthedron.PentagonalHexecontahedron.DH

open NPoly PVec Cap AtlasProjectiveSolutionTree

/-- The certificate's half-turn element is the base's. -/
def pruneOk (c : CapCert) (b : CapBase) : Bool :=
  match b.prune with
  | none => !c.usePrune
  | some g => c.usePrune &&
      (List.finRange 3).all fun i => (List.finRange 3).all fun j => decide (c.Gcol j i = icoK g i j)

/-- A certificate for base cap `b`. -/
def certForBase (c : CapCert) (b : CapBase) : Bool :=
  c.check && decide (2 ≤ c.st.strongScale) && decide (1 ≤ c.st.mcm) && decide (0 ≤ c.pr.t0) &&
    decide (0 ≤ c.pr.t0m) && keq c.st.x b.x && keq c.st.e1 b.e1 && keq c.st.e2 b.e2 &&
    decide (c.pr.mu0 = b.mu0) && decide (0 ≤ b.mu0) && decide (0 ≤ b.wmax2) && decide (b.wmax2 ≤ 3) &&
    decide (b.wmax2 ≤ 4 * b.mu0 ^ 2) && decide (b.wmax2 ≤ (c.st.strongScale : ℚ) ^ 2 * b.mu0 ^ 4) &&
    sameSlots c.verts.toList && pruneOk c b

theorem sqrt_le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hy] at this

theorem baseClaim_of_cert (c : CapCert) (b : CapBase) (h : certForBase c b = true) :
    CapClaim dhIModel.toC5.polyhedron.hull (kv b.x) (kv b.e1) (kv b.e2) b.mu0
      ((3 - b.wmax2) / (1 + b.wmax2)) (b.prune.map icoMatrix) := by
  simp only [certForBase, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, hS⟩, hmcm⟩, ht0⟩, ht0m⟩, hx⟩, he1⟩, he2⟩, hmu⟩, hmu0⟩, hw0⟩, hw3⟩, hw1⟩, hw2⟩,
    hslots⟩, hprune⟩ := h
  have hmu0R : (0 : ℝ) ≤ (b.mu0 : ℝ) := by exact_mod_cast hmu0
  have hw0R : (0 : ℝ) ≤ (b.wmax2 : ℝ) := by exact_mod_cast hw0
  set wmax := √(b.wmax2 : ℝ)
  have hwsq : wmax ^ 2 = (b.wmax2 : ℝ) := Real.sq_sqrt hw0R
  have hclaim := CapCert.claim c hc hS hmcm (by exact_mod_cast ht0) (by exact_mod_cast ht0m) wmax
    (Real.sqrt_nonneg _) (by rw [hwsq]; exact_mod_cast hw3)
    (by
      rw [hmu]
      apply sqrt_le_of_sq (by positivity)
      have : ((b.wmax2 : ℚ) : ℝ) ≤ ((4 * b.mu0 ^ 2 : ℚ) : ℝ) := by exact_mod_cast hw1
      push_cast at this
      nlinarith)
    (by
      rw [hmu]
      apply sqrt_le_of_sq (by positivity)
      have : ((b.wmax2 : ℚ) : ℝ) ≤ (((c.st.strongScale : ℚ) ^ 2 * b.mu0 ^ 4 : ℚ) : ℝ) := by exact_mod_cast hw2
      push_cast at this
      nlinarith)
    (dhScale : ℝ) dhScale_pos _ (dhHull_eq _ hslots) dhIModel_centrallySymmetric
  rw [eq_of_keq hx, eq_of_keq he1, eq_of_keq he2, hmu, hwsq] at hclaim
  convert hclaim using 1
  unfold pruneOk at hprune
  cases hb : b.prune with
  | none =>
    rw [hb] at hprune
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hprune
    simp [hprune]
  | some g =>
    rw [hb] at hprune
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
      decide_eq_true_eq] at hprune
    simp only [Option.map_some, hprune.1, if_true, Option.some.injEq]
    ext i j
    rw [gMat, hprune.2 i j, val_icoK]

/-- One certificate per base cap. -/
def capsCheck (certs : Array CapCert) : Bool :=
  (List.range dhCapBases.size).all fun k =>
    match dhCapBases[k]?, certs[k]? with
    | some b, some c => certForBase c b
    | _, _ => false

/-- **The caps hold** for the exact solid, given checked certificates. -/
theorem capsHold_of_certs (certs : Array CapCert) (h : capsCheck certs = true) :
    CapsHold dhIModel.toC5.polyhedron.hull := by
  intro cap img _ b hb
  apply imgClaim_of_base dhIModel b ?_ img
  simp only [capsCheck, List.all_eq_true, List.mem_range] at h
  have hlt : img.base < dhCapBases.size := by
    by_contra hge
    rw [Array.getElem?_eq_none (by omega)] at hb
    cases hb
  have hk := h img.base hlt
  rw [hb] at hk
  split at hk
  · rename_i b' c hb' hc
    cases hb'
    exact baseClaim_of_cert c b hk
  · simp_all

end Noperthedron.PentagonalHexecontahedron.DH
