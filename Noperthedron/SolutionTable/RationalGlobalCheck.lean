import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Noperthedron.SolutionTable.RationalLocalCheck
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.Nopert

namespace Solution

open scoped RealInnerProductSpace Real
open RationalApprox.GlobalTheorem

noncomputable section

abbrev Row.globalPose (row : Row) : Pose := row.localPose

abbrev Row.globalEps (row : Row) : ℝ := row.localEps

abbrev Row.globalPoseInFourIntervalBool (row : Row) : Bool :=
  row.localPoseInFourIntervalBool

abbrev Row.globalEpsPosBool (row : Row) : Bool :=
  row.localEpsPosBool

def Row.wUnitCheckBool (row : Row) : Bool :=
  decide row.wUnitCheck

lemma wUnitCheckBool_sound (row : Row) :
    row.wUnitCheckBool = true → ‖row.w‖ = 1 := by
  intro h
  have hw : row.wUnitCheck := decide_true_iff h
  exact Row.w_unit_of_wUnitCheck row hw

def Row.globalPreconditionCheck (row : Row) (S : ℝ³) : Prop :=
  row.nodeType = 1 ∧
    fourInterval.contains row.globalPose ∧
    0 < row.globalEps ∧
    row.wUnitCheck ∧
    S ∈ Nopert.poly.vertices ∧
    Gℚ row.globalPose row.globalEps S row.w >
      maxHℚ row.globalPose Nopert.poly row.globalEps row.w

def Row.globalPreconditionCheck_to_precondition (row : Row) (S : ℝ³)
    (h : row.globalPreconditionCheck S) :
    RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
      Nopert.poly Nopert.poly (RationalApprox.κApproxPoly.refl Nopert.poly)
      row.globalPose row.globalEps := by
  rcases h with ⟨_hnode, hp4, hε, hw, hS, hEx⟩
  refine {
    S := S
    S_in_poly := hS
    p_in_4 := hp4
    w := row.w
    w_unit := Row.w_unit_of_wUnitCheck row hw
    exceeds := hEx
  }

structure GlobalPrecheckAlg where
  S : Row → ℝ³
  exceeds : Row → Bool
  S_in_poly_sound : ∀ row, S row ∈ Nopert.poly.vertices
  exceeds_sound :
    ∀ row, exceeds row = true →
      Gℚ row.globalPose row.globalEps (S row) row.w >
        maxHℚ row.globalPose Nopert.poly row.globalEps row.w

def Row.globalPreconditionCheckSpec (row : Row) (alg : GlobalPrecheckAlg) : Prop :=
  row.nodeType = 1 ∧
    row.globalPoseInFourIntervalBool = true ∧
    row.globalEpsPosBool = true ∧
    row.wUnitCheckBool = true ∧
    alg.exceeds row = true

instance (row : Row) (alg : GlobalPrecheckAlg) :
    Decidable (row.globalPreconditionCheckSpec alg) := by
  classical
  unfold Row.globalPreconditionCheckSpec
  infer_instance

def Row.globalPreconditionCheckBool (row : Row) (alg : GlobalPrecheckAlg) : Bool :=
  decide (row.globalPreconditionCheckSpec alg)

theorem globalPreconditionCheckBool_sound (row : Row) (alg : GlobalPrecheckAlg) :
    row.globalPreconditionCheckBool alg = true →
    row.globalPreconditionCheck (alg.S row) := by
  intro h
  have h' : row.globalPreconditionCheckSpec alg := decide_true_iff h
  rcases h' with ⟨hnode, h4, hεb, hwb, hex⟩
  have h4' : fourInterval.contains row.globalPose :=
    localPoseInFourIntervalBool_sound row h4
  have hε : 0 < row.globalEps := localEpsPosBool_sound row hεb
  have hw : row.wUnitCheck := decide_true_iff hwb
  have hS : alg.S row ∈ Nopert.poly.vertices := alg.S_in_poly_sound row
  have hEx := alg.exceeds_sound row hex
  exact ⟨hnode, h4', hε, hw, hS, hEx⟩

structure GlobalPrecheckCertificateData where
  S : Array ℝ³
  exceeds_ok : Array Bool

def Row.globalPreconditionCheckBoolFromData (row : Row)
    (data : GlobalPrecheckCertificateData) : Bool :=
  decide (row.nodeType = 1) &&
    row.globalPoseInFourIntervalBool &&
    row.globalEpsPosBool &&
    row.wUnitCheckBool &&
    oracleGet data.exceeds_ok row.ID

def Table.globalPreconditionCheckBoolFromData (tab : Table)
    (data : GlobalPrecheckCertificateData) : Bool :=
  tab.foldl (fun ok row => ok && row.globalPreconditionCheckBoolFromData data) true

structure GlobalExceedsCert (row : Row) where
  S : ℝ³
  sound :
    Gℚ row.globalPose row.globalEps S row.w >
      maxHℚ row.globalPose Nopert.poly row.globalEps row.w

structure GlobalExceedsRealData (row : Row) where
  S : ℝ³
  g_val : ℝ
  h_val : ℝ

def GlobalExceedsRealData.ofRow (row : Row) (S : ℝ³) : GlobalExceedsRealData row := {
  S := S
  g_val := Gℚ row.globalPose row.globalEps S row.w
  h_val := maxHℚ row.globalPose Nopert.poly row.globalEps row.w
}

noncomputable def ratLower (x : ℝ) (n : ℕ) : ℚ :=
  if h : n = 0 then 0 else (Int.floor (x * n) : ℚ) / n

noncomputable def ratUpper (x : ℝ) (n : ℕ) : ℚ :=
  if h : n = 0 then 0 else (Int.ceil (x * n) : ℚ) / n

lemma ratLower_le (x : ℝ) {n : ℕ} (hn : 0 < n) :
    (ratLower x n : ℝ) ≤ x := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp [ratLower, hn0]
  have hfloor : ((Int.floor (x * n) : ℚ) : ℝ) ≤ x * n := by
    simpa using (Int.floor_le (x * n))
  have hdiv : ((Int.floor (x * n) : ℚ) : ℝ) / (n : ℝ) ≤ x := by
    have := (div_le_iff₀ hn').2 hfloor
    simpa [mul_comm] using this
  simpa using hdiv

lemma le_ratUpper (x : ℝ) {n : ℕ} (hn : 0 < n) :
    x ≤ (ratUpper x n : ℝ) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp [ratUpper, hn0]
  have hceil : x * n ≤ ((Int.ceil (x * n) : ℚ) : ℝ) := by
    simpa using (Int.le_ceil (x * n))
  have hdiv : x ≤ ((Int.ceil (x * n) : ℚ) : ℝ) / (n : ℝ) := by
    have := (le_div_iff₀ hn').2 hceil
    simpa [mul_comm] using this
  simpa using hdiv

structure GlobalExceedsWitness (row : Row) where
  S : ℝ³
  g_lower : ℚ
  h_upper : ℚ
  g_lower_le :
    (g_lower : ℝ) ≤ Gℚ row.globalPose row.globalEps S row.w
  h_upper_ge :
    maxHℚ row.globalPose Nopert.poly row.globalEps row.w ≤ (h_upper : ℝ)
  gap : (h_upper : ℝ) < (g_lower : ℝ)

def Row.globalPrecheckWitnessOK (row : Row) (w : GlobalExceedsWitness row) : Prop :=
  ((w.g_lower : ℝ) ≤ Gℚ row.globalPose row.globalEps w.S row.w) ∧
    (maxHℚ row.globalPose Nopert.poly row.globalEps row.w ≤ (w.h_upper : ℝ)) ∧
    ((w.h_upper : ℝ) < (w.g_lower : ℝ))

lemma exceeds_of_bounds (row : Row) (S : ℝ³) (g_lower h_upper : ℚ)
    (h1 : (g_lower : ℝ) ≤ Gℚ row.globalPose row.globalEps S row.w)
    (h2 : maxHℚ row.globalPose Nopert.poly row.globalEps row.w ≤ (h_upper : ℝ))
    (hgap : (h_upper : ℝ) < (g_lower : ℝ)) :
    Gℚ row.globalPose row.globalEps S row.w >
      maxHℚ row.globalPose Nopert.poly row.globalEps row.w := by
  have h1' :
      maxHℚ row.globalPose Nopert.poly row.globalEps row.w < (g_lower : ℝ) :=
    lt_of_le_of_lt h2 hgap
  have h2' :
      maxHℚ row.globalPose Nopert.poly row.globalEps row.w <
        Gℚ row.globalPose row.globalEps S row.w :=
    lt_of_lt_of_le h1' h1
  simpa [gt_iff_lt] using h2'

def GlobalExceedsWitness.toCert {row : Row} (w : GlobalExceedsWitness row) :
    GlobalExceedsCert row := by
  refine { S := w.S, sound := ?_ }
  exact exceeds_of_bounds row w.S w.g_lower w.h_upper
    w.g_lower_le w.h_upper_ge w.gap

structure GlobalPrecheckRowCert (row : Row) where
  exceeds : GlobalExceedsCert row
  S_in_poly : exceeds.S ∈ Nopert.poly.vertices

structure GlobalPrecheckRowWitness (row : Row) where
  exceeds : GlobalExceedsWitness row
  S_in_poly : exceeds.S ∈ Nopert.poly.vertices

def GlobalPrecheckRowWitness.toRowCert {row : Row} (w : GlobalPrecheckRowWitness row) :
    GlobalPrecheckRowCert row := by
  refine { exceeds := w.exceeds.toCert, S_in_poly := ?_ }
  simpa using w.S_in_poly

structure GlobalPrecheckRowCerts (tab : Table) where
  cert : (row : Row) → row.ID < tab.size → GlobalPrecheckRowCert row

structure GlobalPrecheckCertificateData.ForTable (tab : Table)
    (data : GlobalPrecheckCertificateData) : Prop where
  S : data.S.size = tab.size
  exceeds : data.exceeds_ok.size = tab.size

lemma c1r_in_nopert_verts : Nopert.C1R ∈ Nopert.poly.vertices := by
  have hmem : Nopert.C1R ∈ pointsymmetrize halfNopertVerts := by
    apply (pointsymmetrize_mem halfNopertVerts _).2
    left
    exact c1r_in_half_nopert_verts
  simpa [Nopert.poly, nopertVerts] using hmem

def oracleGetS (arr : Array ℝ³) (id : Nat) : ℝ³ :=
  if h : id < arr.size then arr[(⟨id, h⟩ : Fin arr.size)] else Nopert.C1R

structure GlobalPrecheckCertificate (tab : Table) where
  data : GlobalPrecheckCertificateData
  forTable : GlobalPrecheckCertificateData.ForTable tab data
  S_in_poly :
    ∀ (row : Row) (h : row.ID < tab.size),
      data.S[(⟨row.ID, by simpa [forTable.S] using h⟩ : Fin data.S.size)] ∈
        Nopert.poly.vertices
  exceeds_sound :
    ∀ (row : Row) (h : row.ID < tab.size),
      data.exceeds_ok[(⟨row.ID, by simpa [forTable.exceeds] using h⟩ : Fin data.exceeds_ok.size)] =
        true →
        Gℚ row.globalPose row.globalEps
          data.S[(⟨row.ID, by simpa [forTable.S] using h⟩ : Fin data.S.size)] row.w >
        maxHℚ row.globalPose Nopert.poly row.globalEps row.w

def GlobalPrecheckCertificate.toAlg {tab : Table}
    (cert : GlobalPrecheckCertificate tab) : GlobalPrecheckAlg :=
  { S := fun row => oracleGetS cert.data.S row.ID
    exceeds := fun row => oracleGet cert.data.exceeds_ok row.ID
    S_in_poly_sound := by
      intro row
      by_cases h : row.ID < cert.data.S.size
      · have h' : row.ID < tab.size := by simpa [cert.forTable.S] using h
        have hmem := cert.S_in_poly row h'
        simpa [oracleGetS, h] using hmem
      · simpa [oracleGetS, h] using c1r_in_nopert_verts
    exceeds_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.exceeds_ok row.ID h with ⟨hsize, hval⟩
      have h' : row.ID < tab.size := by simpa [cert.forTable.exceeds] using hsize
      have hs : row.ID < cert.data.S.size := by simpa [cert.forTable.S] using h'
      simpa [oracleGetS, hs] using cert.exceeds_sound row h' hval }

def Row.globalPreconditionCheckBoolFromCert (row : Row)
    {tab : Table} (cert : GlobalPrecheckCertificate tab) : Bool :=
  row.globalPreconditionCheckBool (GlobalPrecheckCertificate.toAlg cert)

theorem globalPreconditionCheckBoolFromCert_sound (row : Row)
    {tab : Table} (cert : GlobalPrecheckCertificate tab) :
    row.globalPreconditionCheckBoolFromCert (tab := tab) cert = true →
    row.globalPreconditionCheck ((GlobalPrecheckCertificate.toAlg cert).S row) := by
  intro h
  exact globalPreconditionCheckBool_sound row (GlobalPrecheckCertificate.toAlg cert) h

def GlobalPrecheckRowCerts.toAlg {tab : Table}
    (certs : GlobalPrecheckRowCerts tab) : GlobalPrecheckAlg :=
  { S := fun row =>
      if h : row.ID < tab.size then (certs.cert row h).exceeds.S else Nopert.C1R
    exceeds := fun row => if h : row.ID < tab.size then true else false
    S_in_poly_sound := by
      intro row
      by_cases h : row.ID < tab.size
      · simpa [h] using (certs.cert row h).S_in_poly
      · simpa [h] using c1r_in_nopert_verts
    exceeds_sound := by
      intro row hval
      by_cases h : row.ID < tab.size
      · simpa [h] using (certs.cert row h).exceeds.sound
      · have hfalse : False := by simpa [h] using hval
        exact (False.elim hfalse) }

def Row.globalPreconditionCheckBoolFromRowCerts (row : Row)
    {tab : Table} (certs : GlobalPrecheckRowCerts tab) : Bool :=
  row.globalPreconditionCheckBool (GlobalPrecheckRowCerts.toAlg certs)

def Table.globalPreconditionCheckBoolFromRowCerts (tab : Table)
    (certs : GlobalPrecheckRowCerts tab) : Bool :=
  tab.foldl (fun ok row => ok && row.globalPreconditionCheckBoolFromRowCerts certs) true

theorem globalPreconditionCheckBoolFromRowCerts_sound (row : Row)
    {tab : Table} (certs : GlobalPrecheckRowCerts tab) :
    row.globalPreconditionCheckBoolFromRowCerts (tab := tab) certs = true →
    row.globalPreconditionCheck ((GlobalPrecheckRowCerts.toAlg certs).S row) := by
  intro h
  exact globalPreconditionCheckBool_sound row (GlobalPrecheckRowCerts.toAlg certs) h

end

end Solution
