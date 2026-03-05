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
      maxHℚ row.globalPose Nopert.poly.toApproxGoodPoly row.globalEps row.w

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
        maxHℚ row.globalPose Nopert.poly.toApproxGoodPoly row.globalEps row.w

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

structure GlobalExceedsCert (row : Row) where
  S : ℝ³
  sound :
    Gℚ row.globalPose row.globalEps S row.w >
      maxHℚ row.globalPose Nopert.poly.toApproxGoodPoly row.globalEps row.w

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
        maxHℚ row.globalPose Nopert.poly.toApproxGoodPoly row.globalEps row.w

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

end

end Solution
