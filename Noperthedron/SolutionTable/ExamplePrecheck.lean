import Noperthedron.SolutionTable.Basic
import Noperthedron.ComputationalStep
import Noperthedron.EuclideanSpaceNotation

namespace Solution

def exampleInterval : Interval := {
  min := fun _ => 0
  max := fun _ => 1
}

def zeroVec3 : ℝ³ := fun _ => 0

def exampleRowGlobal : Row := {
  ID := 0
  nodeType := 1
  nrChildren := 0
  IDfirstChild := 0
  split := 0
  interval := exampleInterval
  S_index := ⟨0, by decide⟩
  wx_numerator := 1
  wy_numerator := 0
  w_denominator := 1
  P1_index := 0
  P2_index := 0
  P3_index := 0
  Q1_index := 0
  Q2_index := 0
  Q3_index := 0
  r := 1
  sigma_Q := by
    simpa using (Finset.Icc (0 : ℕ) 1)
}

def exampleRowLocal : Row := {
  ID := 1
  nodeType := 2
  nrChildren := 0
  IDfirstChild := 0
  split := 0
  interval := exampleInterval
  S_index := ⟨0, by decide⟩
  wx_numerator := 1
  wy_numerator := 0
  w_denominator := 1
  P1_index := 0
  P2_index := 0
  P3_index := 0
  Q1_index := 0
  Q2_index := 0
  Q3_index := 0
  r := 1
  sigma_Q := by
    simpa using (Finset.Icc (0 : ℕ) 1)
}

def exampleTable : Table := #[
  exampleRowGlobal,
  exampleRowLocal
]

def exampleLocalOk : LocalPrecheckCertificateData := {
  boundR_ok := #[true, true]
  boundDelta_ok := #[true, true]
  ae1_ok := #[true, true]
  ae2_ok := #[true, true]
  span1_ok := #[true, true]
  span2_ok := #[true, true]
  be_ok := #[true, true]
}

def exampleGlobalOk : GlobalPrecheckCertificateData := {
  S := #[zeroVec3, zeroVec3]
  exceeds_ok := #[true, true]
}

def examplePrecheckData : SolutionTablePrecheckData := {
  localData := exampleLocalOk
  globalData := exampleGlobalOk
}

def exampleCongruenceOk : Array Bool := #[true, true]

def examplePrecheck : Bool :=
  solutionTablePrecheckBoolWithCongruence
    exampleTable examplePrecheckData exampleCongruenceOk

end Solution
