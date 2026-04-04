import Noperthedron.SolutionTable.RationalLocalCheck.Computable.Oracle

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox (κ)

noncomputable section

/-!
### Per-row certificate wrappers

These package up concrete witnesses for the expensive rational local checks, and turn them into a
`LocalPrecheckCertificate` that always returns `true` on every row.
-/

structure BoundRℚCert (row : Row) (sl : RationalApprox.LowerSqrt) where
  lower : Fin 3 → ℚ
  sound :
    RationalApprox.LocalTheorem.BoundRℚ (row.localR) (row.localEps) row.localPose
      (Row.QTriangle row) sl

structure BoundDeltaℚCert (row : Row) (su : RationalApprox.UpperSqrt) where
  upper : Fin 3 → ℚ
  sound :
    RationalApprox.LocalTheorem.BoundDeltaℚ (row.localDelta su) row.localPose (Row.PTriangle row)
      (Row.QTriangle row) su

structure AεℚCert (tri : Local.Triangle) (X : ℝ³) (ε : ℝ) where
  sigma : ℤ
  bounds : Fin 3 → ℚ
  sound : tri.Aεℚ X ε

structure κSpanningCert (tri : Local.Triangle) (θ φ ε : ℝ) where
  bounds : Fin 3 → ℚ
  sound : tri.κSpanning θ φ ε

structure BεℚCert (tri : Local.Triangle) (p : Pose) (ε δ r : ℝ) (su : RationalApprox.UpperSqrt)
    where
  bounds : Fin 3 → ℚ
  sound : tri.Bεℚ Nopert.poly.vertices p ε δ r su

structure LocalPrecheckRowCert (row : Row) (su : RationalApprox.UpperSqrt)
    (sl : RationalApprox.LowerSqrt) where
  boundR : BoundRℚCert row sl
  boundDelta : BoundDeltaℚCert row su
  ae1 : AεℚCert (Row.PTriangle row) row.localPose.vecX₁ℚ row.localEps
  ae2 : AεℚCert (Row.QTriangle row) row.localPose.vecX₂ℚ row.localEps
  span1 : κSpanningCert (Row.PTriangle row) row.localPose.θ₁ row.localPose.φ₁ row.localEps
  span2 : κSpanningCert (Row.QTriangle row) row.localPose.θ₂ row.localPose.φ₂ row.localEps
  be :
    BεℚCert (Row.QTriangle row) row.localPose row.localEps (row.localDelta su) (row.localR) su

structure LocalPrecheckRowCerts (tab : Table) (su : RationalApprox.UpperSqrt)
    (sl : RationalApprox.LowerSqrt) where
  cert : (row : Row) → row.ID < tab.size → LocalPrecheckRowCert row su sl

def LocalPrecheckRowCerts.toCertificate {tab : Table} {su : RationalApprox.UpperSqrt}
    {sl : RationalApprox.LowerSqrt} (certs : LocalPrecheckRowCerts tab su sl) :
    LocalPrecheckCertificate tab su sl := by
  classical
  refine {
    data := {
      boundR_ok := Array.replicate tab.size true
      boundDelta_ok := Array.replicate tab.size true
      ae1_ok := Array.replicate tab.size true
      ae2_ok := Array.replicate tab.size true
      span1_ok := Array.replicate tab.size true
      span2_ok := Array.replicate tab.size true
      be_ok := Array.replicate tab.size true
    }
    forTable := by
      refine {
        boundR := ?_
        boundDelta := ?_
        ae1 := ?_
        ae2 := ?_
        span1 := ?_
        span2 := ?_
        be := ?_
      } <;> simp
    boundR_sound := by
      intro row h _hval
      exact (certs.cert row h).boundR.sound
    boundDelta_sound := by
      intro row h _hval
      exact (certs.cert row h).boundDelta.sound
    ae1_sound := by
      intro row h _hval
      exact (certs.cert row h).ae1.sound
    ae2_sound := by
      intro row h _hval
      exact (certs.cert row h).ae2.sound
    span1_sound := by
      intro row h _hval
      exact (certs.cert row h).span1.sound
    span2_sound := by
      intro row h _hval
      exact (certs.cert row h).span2.sound
    be_sound := by
      intro row h _hval
      exact (certs.cert row h).be.sound
  }

end

end Solution
