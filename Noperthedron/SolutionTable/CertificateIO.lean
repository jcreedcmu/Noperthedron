import Lean
import Noperthedron.EuclideanSpaceNotation
import Noperthedron.SolutionTable.RationalLocalCheck
import Noperthedron.SolutionTable.RationalGlobalCheck

namespace Solution

open Lean

def jsonObj (j : Json) : Except String (Std.RBMap String Json compare) :=
  match j with
  | Json.obj o => pure o
  | _ => throw "expected JSON object"

def jsonArr (j : Json) : Except String (Array Json) :=
  match j with
  | Json.arr a => pure a
  | _ => throw "expected JSON array"

def jsonField (o : Std.RBMap String Json compare) (k : String) : Except String Json :=
  match o.find? k with
  | some v => pure v
  | none => throw s!"missing field {k}"

def jsonBool (j : Json) : Except String Bool :=
  fromJson? j

def jsonInt (j : Json) : Except String Int :=
  fromJson? j

def jsonIntOr (j : Json) (default : Int) : Except String Int :=
  match j with
  | Json.null => pure default
  | _ => jsonInt j

def jsonRat (j : Json) : Except String ℚ := do
  let o <- jsonObj j
  let numJ <- jsonField o "num"
  let denJ <- jsonField o "den"
  let num <- jsonInt numJ
  let den <- jsonInt denJ
  if den = 0 then
    throw "den must be nonzero"
  pure ((num : ℚ) / (den : ℚ))

def jsonRat3 (j : Json) : Except String ℝ³ := do
  let arr <- jsonArr j
  match arr.toList with
  | [a, b, c] =>
      let ra <- jsonRat a
      let rb <- jsonRat b
      let rc <- jsonRat c
      pure (fun i =>
        match i.1 with
        | 0 => (ra : ℝ)
        | 1 => (rb : ℝ)
        | _ => (rc : ℝ))
  | _ => throw "expected array of length 3"

def jsonBoolArray (j : Json) : Except String (Array Bool) := do
  let arr <- jsonArr j
  arr.mapM jsonBool

def congruenceOkFromArray (arr : Array Bool) (row : Row) : Bool :=
  if h : row.ID < arr.size then arr[⟨row.ID, h⟩] else false

def jsonRowInterval (o : Std.RBMap String Json compare) : Except String Interval := do
  let t1min <- jsonInt (← jsonField o "T1_min")
  let t1max <- jsonInt (← jsonField o "T1_max")
  let v1min <- jsonInt (← jsonField o "V1_min")
  let v1max <- jsonInt (← jsonField o "V1_max")
  let t2min <- jsonInt (← jsonField o "T2_min")
  let t2max <- jsonInt (← jsonField o "T2_max")
  let v2min <- jsonInt (← jsonField o "V2_min")
  let v2max <- jsonInt (← jsonField o "V2_max")
  let amin <- jsonInt (← jsonField o "A_min")
  let amax <- jsonInt (← jsonField o "A_max")
  pure {
    min := fun
      | .θ₁ => t1min
      | .φ₁ => v1min
      | .θ₂ => t2min
      | .φ₂ => v2min
      | .α => amin
    max := fun
      | .θ₁ => t1max
      | .φ₁ => v1max
      | .θ₂ => t2max
      | .φ₂ => v2max
      | .α => amax
  }

def jsonNatOr (j : Json) (default : Nat) : Except String Nat := do
  let i <- jsonIntOr j default
  if i < 0 then
    throw "expected nonnegative integer"
  pure i.toNat

def jsonRow (j : Json) : Except String Row := do
  let o <- jsonObj j
  let id <- jsonNatOr (← jsonField o "ID") 0
  let nodeType <- jsonNatOr (← jsonField o "nodeType") 0
  let nrChildren <- jsonNatOr (← jsonField o "nrChildren") 0
  let idFirstChild <- jsonNatOr (← jsonField o "IDfirstChild") 0
  let split <- jsonNatOr (← jsonField o "split") 0
  let interval <- jsonRowInterval o
  let sIndex <- jsonNatOr (← jsonField o "S_index") 0
  let wx <- jsonIntOr (← jsonField o "wx_nominator") 0
  let wy <- jsonIntOr (← jsonField o "wy_nominator") 0
  let wDen <- jsonNatOr (← jsonField o "w_denominator") 1
  let p1 <- jsonNatOr (← jsonField o "P1_index") 0
  let p2 <- jsonNatOr (← jsonField o "P2_index") 0
  let p3 <- jsonNatOr (← jsonField o "P3_index") 0
  let q1 <- jsonNatOr (← jsonField o "Q1_index") 0
  let q2 <- jsonNatOr (← jsonField o "Q2_index") 0
  let q3 <- jsonNatOr (← jsonField o "Q3_index") 0
  let r <- jsonIntOr (← jsonField o "r") 0
  if h : sIndex < 90 then
    pure {
      ID := id
      nodeType := nodeType
      nrChildren := nrChildren
      IDfirstChild := idFirstChild
      split := split
      interval := interval
      S_index := ⟨sIndex, h⟩
      wx_numerator := wx
      wy_numerator := wy
      w_denominator := wDen
      P1_index := p1
      P2_index := p2
      P3_index := p3
      Q1_index := q1
      Q2_index := q2
      Q3_index := q3
      r := r
      sigma_Q := by
        simpa using (Finset.Icc (0 : ℕ) 1)
    }
  else
    throw "S_index out of range"

def parseTable (j : Json) : Except String Table := do
  let o <- jsonObj j
  let rows <- jsonArr (← jsonField o "rows")
  rows.mapM jsonRow

def parseLocalOk (j : Json) : Except String LocalPrecheckCertificateData := do
  let o <- jsonObj j
  let boundR <- jsonBoolArray (← jsonField o "bound_r_ok")
  let boundDelta <- jsonBoolArray (← jsonField o "bound_delta_ok")
  let ae1 <- jsonBoolArray (← jsonField o "ae1_ok")
  let ae2 <- jsonBoolArray (← jsonField o "ae2_ok")
  let span1 <- jsonBoolArray (← jsonField o "span1_ok")
  let span2 <- jsonBoolArray (← jsonField o "span2_ok")
  let be <- jsonBoolArray (← jsonField o "be_ok")
  pure {
    boundR_ok := boundR
    boundDelta_ok := boundDelta
    ae1_ok := ae1
    ae2_ok := ae2
    span1_ok := span1
    span2_ok := span2
    be_ok := be
  }

def parseGlobalOk (j : Json) : Except String GlobalPrecheckCertificateData := do
  let o <- jsonObj j
  let sArr <- jsonArr (← jsonField o "S")
  let S <- sArr.mapM jsonRat3
  let exceeds <- jsonBoolArray (← jsonField o "exceeds_ok")
  pure {
    S := S
    exceeds_ok := exceeds
  }

def parsePrecheckData (j : Json) : Except String SolutionTablePrecheckData := do
  let o <- jsonObj j
  let localJ <- jsonField o "local_ok"
  let globalJ <- jsonField o "global_ok"
  let local <- parseLocalOk localJ
  let global <- parseGlobalOk globalJ
  pure { localData := local, globalData := global }

def parseCongruenceOk (j : Json) : Except String (Array Bool) :=
  jsonBoolArray j

def parseTableAndPrecheck (j : Json) : Except String (Table × SolutionTablePrecheckData × Array Bool) := do
  let tab <- parseTable j
  let data <- parsePrecheckData j
  let o <- jsonObj j
  let congruence <- parseCongruenceOk (← jsonField o "congruence_ok")
  pure (tab, data, congruence)

end Solution
