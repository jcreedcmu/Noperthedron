import Noperthedron.SolutionTable.RationalLocalCheck.Precondition

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox (κ)

noncomputable section

/-!
### Oracle-backed scaffold

This packages per-row Boolean "oracle" outputs for the expensive rational checks, together with
soundness hypotheses turning `true` into the corresponding mathematical statements.
-/

structure LocalPrecheckAlg (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt) where
  boundR : Row → Bool
  boundDelta : Row → Bool
  ae1 : Row → Bool
  ae2 : Row → Bool
  span1 : Row → Bool
  span2 : Row → Bool
  be : Row → Bool
  boundR_sound :
    ∀ row, boundR row = true →
      RationalApprox.LocalTheorem.BoundRℚ (row.localR) (row.localEps)
        row.localPose (Row.QTriangle row) sl
  boundDelta_sound :
    ∀ row, boundDelta row = true →
      RationalApprox.LocalTheorem.BoundDeltaℚ (row.localDelta su) row.localPose
        (Row.PTriangle row) (Row.QTriangle row) su
  ae1_sound :
    ∀ row, ae1 row = true → (Row.PTriangle row).Aεℚ row.localPose.vecX₁ℚ row.localEps
  ae2_sound :
    ∀ row, ae2 row = true → (Row.QTriangle row).Aεℚ row.localPose.vecX₂ℚ row.localEps
  span1_sound :
    ∀ row, span1 row = true →
      (Row.PTriangle row).κSpanning row.localPose.θ₁ row.localPose.φ₁ row.localEps
  span2_sound :
    ∀ row, span2 row = true →
      (Row.QTriangle row).κSpanning row.localPose.θ₂ row.localPose.φ₂ row.localEps
  be_sound :
    ∀ row, be row = true →
      (Row.QTriangle row).Bεℚ Nopert.poly.vertices row.localPose row.localEps
        (row.localDelta su) (row.localR) su

def oracleGet (arr : Array Bool) (id : Nat) : Bool :=
  if h : id < arr.size then arr[(⟨id, h⟩ : Fin arr.size)] else false

lemma oracleGet_true_iff (arr : Array Bool) (id : Nat) :
    oracleGet arr id = true →
      ∃ h : id < arr.size, arr[(⟨id, h⟩ : Fin arr.size)] = true := by
  intro h
  by_cases h' : id < arr.size
  · refine ⟨h', ?_⟩
    simp [oracleGet, h'] at h
    exact h
  · simp [oracleGet, h'] at h

structure LocalPrecheckOracle (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt) where
  boundR_ok : Array Bool
  boundDelta_ok : Array Bool
  ae1_ok : Array Bool
  ae2_ok : Array Bool
  span1_ok : Array Bool
  span2_ok : Array Bool
  be_ok : Array Bool
  boundR_sound :
    ∀ row, oracleGet boundR_ok row.ID = true →
      RationalApprox.LocalTheorem.BoundRℚ (row.localR) (row.localEps)
        row.localPose (Row.QTriangle row) sl
  boundDelta_sound :
    ∀ row, oracleGet boundDelta_ok row.ID = true →
      RationalApprox.LocalTheorem.BoundDeltaℚ (row.localDelta su) row.localPose
        (Row.PTriangle row) (Row.QTriangle row) su
  ae1_sound :
    ∀ row, oracleGet ae1_ok row.ID = true →
      (Row.PTriangle row).Aεℚ row.localPose.vecX₁ℚ row.localEps
  ae2_sound :
    ∀ row, oracleGet ae2_ok row.ID = true →
      (Row.QTriangle row).Aεℚ row.localPose.vecX₂ℚ row.localEps
  span1_sound :
    ∀ row, oracleGet span1_ok row.ID = true →
      (Row.PTriangle row).κSpanning row.localPose.θ₁ row.localPose.φ₁ row.localEps
  span2_sound :
    ∀ row, oracleGet span2_ok row.ID = true →
      (Row.QTriangle row).κSpanning row.localPose.θ₂ row.localPose.φ₂ row.localEps
  be_sound :
    ∀ row, oracleGet be_ok row.ID = true →
      (Row.QTriangle row).Bεℚ Nopert.poly.vertices row.localPose row.localEps
        (row.localDelta su) (row.localR) su

structure LocalPrecheckCertificateData where
  boundR_ok : Array Bool
  boundDelta_ok : Array Bool
  ae1_ok : Array Bool
  ae2_ok : Array Bool
  span1_ok : Array Bool
  span2_ok : Array Bool
  be_ok : Array Bool

structure LocalPrecheckCertificateData.ForTable (tab : Table)
    (data : LocalPrecheckCertificateData) : Prop where
  boundR : data.boundR_ok.size = tab.size
  boundDelta : data.boundDelta_ok.size = tab.size
  ae1 : data.ae1_ok.size = tab.size
  ae2 : data.ae2_ok.size = tab.size
  span1 : data.span1_ok.size = tab.size
  span2 : data.span2_ok.size = tab.size
  be : data.be_ok.size = tab.size

structure LocalPrecheckCertificate (tab : Table)
    (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt) where
  data : LocalPrecheckCertificateData
  forTable : LocalPrecheckCertificateData.ForTable tab data
  boundR_sound :
    ∀ row (h : row.ID < tab.size),
      oracleGet data.boundR_ok row.ID = true →
        RationalApprox.LocalTheorem.BoundRℚ (row.localR) (row.localEps)
          row.localPose (Row.QTriangle row) sl
  boundDelta_sound :
    ∀ row (h : row.ID < tab.size),
      oracleGet data.boundDelta_ok row.ID = true →
        RationalApprox.LocalTheorem.BoundDeltaℚ (row.localDelta su) row.localPose
          (Row.PTriangle row) (Row.QTriangle row) su
  ae1_sound :
    ∀ row (h : row.ID < tab.size),
      oracleGet data.ae1_ok row.ID = true →
        (Row.PTriangle row).Aεℚ row.localPose.vecX₁ℚ row.localEps
  ae2_sound :
    ∀ row (h : row.ID < tab.size),
      oracleGet data.ae2_ok row.ID = true →
        (Row.QTriangle row).Aεℚ row.localPose.vecX₂ℚ row.localEps
  span1_sound :
    ∀ row (h : row.ID < tab.size),
      oracleGet data.span1_ok row.ID = true →
        (Row.PTriangle row).κSpanning row.localPose.θ₁ row.localPose.φ₁ row.localEps
  span2_sound :
    ∀ row (h : row.ID < tab.size),
      oracleGet data.span2_ok row.ID = true →
        (Row.QTriangle row).κSpanning row.localPose.θ₂ row.localPose.φ₂ row.localEps
  be_sound :
    ∀ row (h : row.ID < tab.size),
      oracleGet data.be_ok row.ID = true →
        (Row.QTriangle row).Bεℚ Nopert.poly.vertices row.localPose row.localEps
          (row.localDelta su) (row.localR) su

def LocalPrecheckCertificate.toOracle {tab : Table}
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (cert : LocalPrecheckCertificate tab su sl) : LocalPrecheckOracle su sl :=
  { boundR_ok := cert.data.boundR_ok
    boundDelta_ok := cert.data.boundDelta_ok
    ae1_ok := cert.data.ae1_ok
    ae2_ok := cert.data.ae2_ok
    span1_ok := cert.data.span1_ok
    span2_ok := cert.data.span2_ok
    be_ok := cert.data.be_ok
    boundR_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.boundR_ok row.ID h with ⟨hsize, _hval⟩
      have htab : row.ID < tab.size := Nat.lt_of_lt_of_eq hsize cert.forTable.boundR
      exact cert.boundR_sound row htab h
    boundDelta_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.boundDelta_ok row.ID h with ⟨hsize, _hval⟩
      have htab : row.ID < tab.size := Nat.lt_of_lt_of_eq hsize cert.forTable.boundDelta
      exact cert.boundDelta_sound row htab h
    ae1_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.ae1_ok row.ID h with ⟨hsize, _hval⟩
      have htab : row.ID < tab.size := Nat.lt_of_lt_of_eq hsize cert.forTable.ae1
      exact cert.ae1_sound row htab h
    ae2_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.ae2_ok row.ID h with ⟨hsize, _hval⟩
      have htab : row.ID < tab.size := Nat.lt_of_lt_of_eq hsize cert.forTable.ae2
      exact cert.ae2_sound row htab h
    span1_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.span1_ok row.ID h with ⟨hsize, _hval⟩
      have htab : row.ID < tab.size := Nat.lt_of_lt_of_eq hsize cert.forTable.span1
      exact cert.span1_sound row htab h
    span2_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.span2_ok row.ID h with ⟨hsize, _hval⟩
      have htab : row.ID < tab.size := Nat.lt_of_lt_of_eq hsize cert.forTable.span2
      exact cert.span2_sound row htab h
    be_sound := by
      intro row h
      rcases oracleGet_true_iff cert.data.be_ok row.ID h with ⟨hsize, _hval⟩
      have htab : row.ID < tab.size := Nat.lt_of_lt_of_eq hsize cert.forTable.be
      exact cert.be_sound row htab h }

def LocalPrecheckAlg.ofOracle {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (oracle : LocalPrecheckOracle su sl) : LocalPrecheckAlg su sl :=
  { boundR := fun row => oracleGet oracle.boundR_ok row.ID
    boundDelta := fun row => oracleGet oracle.boundDelta_ok row.ID
    ae1 := fun row => oracleGet oracle.ae1_ok row.ID
    ae2 := fun row => oracleGet oracle.ae2_ok row.ID
    span1 := fun row => oracleGet oracle.span1_ok row.ID
    span2 := fun row => oracleGet oracle.span2_ok row.ID
    be := fun row => oracleGet oracle.be_ok row.ID
    boundR_sound := by
      intro row h
      exact oracle.boundR_sound row h
    boundDelta_sound := by
      intro row h
      exact oracle.boundDelta_sound row h
    ae1_sound := by
      intro row h
      exact oracle.ae1_sound row h
    ae2_sound := by
      intro row h
      exact oracle.ae2_sound row h
    span1_sound := by
      intro row h
      exact oracle.span1_sound row h
    span2_sound := by
      intro row h
      exact oracle.span2_sound row h
    be_sound := by
      intro row h
      exact oracle.be_sound row h }

end

end Solution
