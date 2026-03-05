import Noperthedron.SolutionTable.RationalLocalCheck.Computable.BasicChecks
import Noperthedron.SolutionTable.RationalLocalCheck.Computable.Oracle

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox (κ)

noncomputable section

/-!
### Bool wrapper + soundness

Combine the basic checks with an oracle/algorithm for the expensive rational inequalities.
-/

def Row.localPreconditionCheckBool (row : Row)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (alg : LocalPrecheckAlg su sl) : Bool :=
  decide (row.nodeType = 2) &&
    (row.localPoseInFourIntervalBool &&
      (row.localEpsPosBool &&
        (row.localRPosBool &&
          (alg.boundR row &&
            (alg.boundDelta row &&
              (alg.ae1 row &&
                (alg.ae2 row &&
                  (alg.span1 row &&
                    (alg.span2 row && alg.be row)))))))))

def Row.localPreconditionCheckBoolFromData (row : Row)
    (data : LocalPrecheckCertificateData) : Bool :=
  decide (row.nodeType = 2) &&
    row.localPoseInFourIntervalBool &&
    row.localEpsPosBool &&
    row.localRPosBool &&
    oracleGet data.boundR_ok row.ID &&
    oracleGet data.boundDelta_ok row.ID &&
    oracleGet data.ae1_ok row.ID &&
    oracleGet data.ae2_ok row.ID &&
    oracleGet data.span1_ok row.ID &&
    oracleGet data.span2_ok row.ID &&
    oracleGet data.be_ok row.ID

def Row.localPreconditionCheckBoolFromCert (row : Row)
    {tab : Table} {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (cert : LocalPrecheckCertificate tab su sl) : Bool :=
  row.localPreconditionCheckBool
    (LocalPrecheckAlg.ofOracle (LocalPrecheckCertificate.toOracle cert))

theorem localPreconditionCheckBool_sound (row : Row)
    {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (alg : LocalPrecheckAlg su sl) :
    row.localPreconditionCheckBool alg = true →
    row.localPreconditionCheck su sl := by
  intro h
  unfold Row.localPreconditionCheckBool at h
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hnodeB, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hfourB, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hεb, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hrb, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hR, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hΔ, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hae1, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hae2, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hspan1, h⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨hspan2, hbe⟩

  have hnode : row.nodeType = 2 := decide_true_iff hnodeB
  have hfour : fourInterval.contains row.localPose :=
    localPoseInFourIntervalBool_sound row hfourB
  have hε : 0 < row.localEps := localEpsPosBool_sound row hεb
  have hr : 0 < row.localR := localRPosBool_sound row hrb
  have hR' := alg.boundR_sound row hR
  have hΔ' := alg.boundDelta_sound row hΔ
  have hae1' := alg.ae1_sound row hae1
  have hae2' := alg.ae2_sound row hae2
  have hspan1' := alg.span1_sound row hspan1
  have hspan2' := alg.span2_sound row hspan2
  have hbe' := alg.be_sound row hbe
  exact ⟨hnode, hfour, hε, hr, hR', hΔ', hae1', hae2', hspan1', hspan2', hbe'⟩

theorem localPreconditionCheckBoolFromCert_sound (row : Row)
    {tab : Table} {su : RationalApprox.UpperSqrt} {sl : RationalApprox.LowerSqrt}
    (cert : LocalPrecheckCertificate tab su sl) :
    row.localPreconditionCheckBoolFromCert (tab := tab) cert = true →
    row.localPreconditionCheck su sl := by
  intro h
  exact localPreconditionCheckBool_sound row
    (LocalPrecheckAlg.ofOracle (LocalPrecheckCertificate.toOracle cert)) h

end

end Solution
