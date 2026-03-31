import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Congruence
import Noperthedron.RationalApprox.RationalLocal
import Noperthedron.PoseInterval
import Noperthedron.Nopert

namespace Solution

open scoped RealInnerProductSpace Real
open Local (Triangle)
open RationalApprox (κ)

noncomputable section

/-- The denominator used for the `r` column in the solution table. -/
def R_DENOMINATOR : ℝ := 1000

lemma mem_pose_interval_iff (q : Pose) (iv : Interval) :
    q ∈ iv.toPoseInterval ↔
      q.θ₁ ∈ Set.Icc (iv.min .θ₁ / DENOM) (iv.max .θ₁ / DENOM) ∧
      q.φ₁ ∈ Set.Icc (iv.min .φ₁ / DENOM) (iv.max .φ₁ / DENOM) ∧
      q.θ₂ ∈ Set.Icc (iv.min .θ₂ / DENOM) (iv.max .θ₂ / DENOM) ∧
      q.φ₂ ∈ Set.Icc (iv.min .φ₂ / DENOM) (iv.max .φ₂ / DENOM) ∧
      q.α ∈ Set.Icc (iv.min .α / DENOM) (iv.max .α / DENOM)
      := by
  constructor <;>
  · simp_all [Interval.toPoseInterval, Membership.mem, PoseInterval.contains]

def Row.intervalMid (row : Row) (p : Param) : ℝ :=
  ((row.interval.min p + row.interval.max p) : ℝ) / (2 * DENOM)

def Row.intervalHalfWidth (row : Row) (p : Param) : ℝ :=
  ((row.interval.max p - row.interval.min p) : ℝ) / (2 * DENOM)

lemma intervalMid_sub_halfWidth (row : Row) (p : Param) :
    row.intervalMid p - row.intervalHalfWidth p = (row.interval.min p : ℝ) / DENOM := by
  have h2denom : (2 * DENOM : ℝ) ≠ 0 := by
    norm_num [DENOM]
  unfold Row.intervalMid Row.intervalHalfWidth
  field_simp [DENOM, h2denom]
  ring_nf

lemma intervalMid_add_halfWidth (row : Row) (p : Param) :
    row.intervalMid p + row.intervalHalfWidth p = (row.interval.max p : ℝ) / DENOM := by
  have h2denom : (2 * DENOM : ℝ) ≠ 0 := by
    norm_num [DENOM]
  unfold Row.intervalMid Row.intervalHalfWidth
  field_simp [DENOM, h2denom]
  ring_nf

/-- Midpoint pose for a local row (matches the notebook construction). -/
def Row.localPose (row : Row) : Pose := {
  θ₁ := row.intervalMid .θ₁
  φ₁ := row.intervalMid .φ₁
  θ₂ := row.intervalMid .θ₂
  φ₂ := row.intervalMid .φ₂
  α := row.intervalMid .α
}

/-- `ε` for a local row: half the maximum interval width. -/
def Row.localEps (row : Row) : ℝ :=
  let eθ₁ := row.intervalHalfWidth .θ₁
  let eφ₁ := row.intervalHalfWidth .φ₁
  let eθ₂ := row.intervalHalfWidth .θ₂
  let eφ₂ := row.intervalHalfWidth .φ₂
  let eα := row.intervalHalfWidth .α
  max eθ₁ (max eφ₁ (max eθ₂ (max eφ₂ eα)))

/-- `r` for a local row (stored with denominator `R_DENOMINATOR`). -/
def Row.localR (row : Row) : ℝ :=
  (row.r : ℝ) / R_DENOMINATOR

lemma intervalHalfWidth_le_localEps (row : Row) (p : Param) :
    row.intervalHalfWidth p ≤ row.localEps := by
  fin_cases p <;> simp [Row.localEps, Row.intervalHalfWidth]

lemma mem_poseInterval_imp_mem_closed_ball (row : Row) (q : Pose)
    (hq : q ∈ row.toPoseInterval) :
    q ∈ row.localPose.closed_ball row.localEps := by
  have hq' := (mem_pose_interval_iff q row.interval).1 hq
  have hθ₁' : q.θ₁ ∈ Set.Icc (row.intervalMid .θ₁ - row.localEps)
      (row.intervalMid .θ₁ + row.localEps) := by
    have hlo : (row.interval.min .θ₁ : ℝ) / DENOM ≤ q.θ₁ := hq'.1.1
    have hhi : q.θ₁ ≤ (row.interval.max .θ₁ : ℝ) / DENOM := hq'.1.2
    have hlow' : row.intervalMid .θ₁ - row.intervalHalfWidth .θ₁ ≤ q.θ₁ := by
      simpa [intervalMid_sub_halfWidth] using hlo
    have hle :
        row.intervalMid .θ₁ - row.localEps ≤ row.intervalMid .θ₁ - row.intervalHalfWidth .θ₁ :=
      sub_le_sub_left (intervalHalfWidth_le_localEps row .θ₁) _
    have hlow : row.intervalMid .θ₁ - row.localEps ≤ q.θ₁ := le_trans hle hlow'
    have hup' : q.θ₁ ≤ row.intervalMid .θ₁ + row.intervalHalfWidth .θ₁ := by
      simpa [intervalMid_add_halfWidth] using hhi
    have hle' :
        row.intervalMid .θ₁ + row.intervalHalfWidth .θ₁ ≤ row.intervalMid .θ₁ + row.localEps :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (intervalHalfWidth_le_localEps row .θ₁) (row.intervalMid .θ₁))
    have hup : q.θ₁ ≤ row.intervalMid .θ₁ + row.localEps := le_trans hup' hle'
    exact ⟨hlow, hup⟩
  have hφ₁' : q.φ₁ ∈ Set.Icc (row.intervalMid .φ₁ - row.localEps)
      (row.intervalMid .φ₁ + row.localEps) := by
    have hlo : (row.interval.min .φ₁ : ℝ) / DENOM ≤ q.φ₁ := hq'.2.1.1
    have hhi : q.φ₁ ≤ (row.interval.max .φ₁ : ℝ) / DENOM := hq'.2.1.2
    have hlow' : row.intervalMid .φ₁ - row.intervalHalfWidth .φ₁ ≤ q.φ₁ := by
      simpa [intervalMid_sub_halfWidth] using hlo
    have hle :
        row.intervalMid .φ₁ - row.localEps ≤ row.intervalMid .φ₁ - row.intervalHalfWidth .φ₁ :=
      sub_le_sub_left (intervalHalfWidth_le_localEps row .φ₁) _
    have hlow : row.intervalMid .φ₁ - row.localEps ≤ q.φ₁ := le_trans hle hlow'
    have hup' : q.φ₁ ≤ row.intervalMid .φ₁ + row.intervalHalfWidth .φ₁ := by
      simpa [intervalMid_add_halfWidth] using hhi
    have hle' :
        row.intervalMid .φ₁ + row.intervalHalfWidth .φ₁ ≤ row.intervalMid .φ₁ + row.localEps :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (intervalHalfWidth_le_localEps row .φ₁) (row.intervalMid .φ₁))
    have hup : q.φ₁ ≤ row.intervalMid .φ₁ + row.localEps := le_trans hup' hle'
    exact ⟨hlow, hup⟩
  have hθ₂' : q.θ₂ ∈ Set.Icc (row.intervalMid .θ₂ - row.localEps)
      (row.intervalMid .θ₂ + row.localEps) := by
    have hlo : (row.interval.min .θ₂ : ℝ) / DENOM ≤ q.θ₂ := hq'.2.2.1.1
    have hhi : q.θ₂ ≤ (row.interval.max .θ₂ : ℝ) / DENOM := hq'.2.2.1.2
    have hlow' : row.intervalMid .θ₂ - row.intervalHalfWidth .θ₂ ≤ q.θ₂ := by
      simpa [intervalMid_sub_halfWidth] using hlo
    have hle :
        row.intervalMid .θ₂ - row.localEps ≤ row.intervalMid .θ₂ - row.intervalHalfWidth .θ₂ :=
      sub_le_sub_left (intervalHalfWidth_le_localEps row .θ₂) _
    have hlow : row.intervalMid .θ₂ - row.localEps ≤ q.θ₂ := le_trans hle hlow'
    have hup' : q.θ₂ ≤ row.intervalMid .θ₂ + row.intervalHalfWidth .θ₂ := by
      simpa [intervalMid_add_halfWidth] using hhi
    have hle' :
        row.intervalMid .θ₂ + row.intervalHalfWidth .θ₂ ≤ row.intervalMid .θ₂ + row.localEps :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (intervalHalfWidth_le_localEps row .θ₂) (row.intervalMid .θ₂))
    have hup : q.θ₂ ≤ row.intervalMid .θ₂ + row.localEps := le_trans hup' hle'
    exact ⟨hlow, hup⟩
  have hφ₂' : q.φ₂ ∈ Set.Icc (row.intervalMid .φ₂ - row.localEps)
      (row.intervalMid .φ₂ + row.localEps) := by
    have hlo : (row.interval.min .φ₂ : ℝ) / DENOM ≤ q.φ₂ := hq'.2.2.2.1.1
    have hhi : q.φ₂ ≤ (row.interval.max .φ₂ : ℝ) / DENOM := hq'.2.2.2.1.2
    have hlow' : row.intervalMid .φ₂ - row.intervalHalfWidth .φ₂ ≤ q.φ₂ := by
      simpa [intervalMid_sub_halfWidth] using hlo
    have hle :
        row.intervalMid .φ₂ - row.localEps ≤ row.intervalMid .φ₂ - row.intervalHalfWidth .φ₂ :=
      sub_le_sub_left (intervalHalfWidth_le_localEps row .φ₂) _
    have hlow : row.intervalMid .φ₂ - row.localEps ≤ q.φ₂ := le_trans hle hlow'
    have hup' : q.φ₂ ≤ row.intervalMid .φ₂ + row.intervalHalfWidth .φ₂ := by
      simpa [intervalMid_add_halfWidth] using hhi
    have hle' :
        row.intervalMid .φ₂ + row.intervalHalfWidth .φ₂ ≤ row.intervalMid .φ₂ + row.localEps :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (intervalHalfWidth_le_localEps row .φ₂) (row.intervalMid .φ₂))
    have hup : q.φ₂ ≤ row.intervalMid .φ₂ + row.localEps := le_trans hup' hle'
    exact ⟨hlow, hup⟩
  have hα' : q.α ∈ Set.Icc (row.intervalMid .α - row.localEps)
      (row.intervalMid .α + row.localEps) := by
    have hlo : (row.interval.min .α : ℝ) / DENOM ≤ q.α := hq'.2.2.2.2.1
    have hhi : q.α ≤ (row.interval.max .α : ℝ) / DENOM := hq'.2.2.2.2.2
    have hlow' : row.intervalMid .α - row.intervalHalfWidth .α ≤ q.α := by
      simpa [intervalMid_sub_halfWidth] using hlo
    have hle :
        row.intervalMid .α - row.localEps ≤ row.intervalMid .α - row.intervalHalfWidth .α :=
      sub_le_sub_left (intervalHalfWidth_le_localEps row .α) _
    have hlow : row.intervalMid .α - row.localEps ≤ q.α := le_trans hle hlow'
    have hup' : q.α ≤ row.intervalMid .α + row.intervalHalfWidth .α := by
      simpa [intervalMid_add_halfWidth] using hhi
    have hle' :
        row.intervalMid .α + row.intervalHalfWidth .α ≤ row.intervalMid .α + row.localEps :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (intervalHalfWidth_le_localEps row .α) (row.intervalMid .α))
    have hup : q.α ≤ row.intervalMid .α + row.localEps := le_trans hup' hle'
    exact ⟨hlow, hup⟩
  simp [Pose.closed_ball, PoseInterval.contains, Row.localPose, Row.intervalMid, Membership.mem]
  exact ⟨hθ₁', hθ₂', hφ₁', hφ₂', hα'⟩

/-- `δ` computed from the midpoint pose and the row triangles. -/
def Row.localDelta (row : Row) (su : RationalApprox.UpperSqrt) : ℝ :=
  let p_ := row.localPose
  let r1 := p_.rotR (p_.rotM₁ℚ (Row.PTriangle row 0)) - p_.rotM₂ℚ (Row.QTriangle row 0)
  let r2 := p_.rotR (p_.rotM₁ℚ (Row.PTriangle row 1)) - p_.rotM₂ℚ (Row.QTriangle row 1)
  let r3 := p_.rotR (p_.rotM₁ℚ (Row.PTriangle row 2)) - p_.rotM₂ℚ (Row.QTriangle row 2)
  3 * κ + (max (su.norm r1) (max (su.norm r2) (su.norm r3))) / 2

/--
Notebook-style local precondition assembled from row fields.

This mirrors the rational checks used for `nodeType = 2` rows, using the row midpoint pose, `ε`,
`r`, and the derived `δ`.
-/
def Row.localPreconditionCheck (row : Row)
    (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt) : Prop :=
  let p_ := row.localPose
  let ε := row.localEps
  let r := row.localR
  let δ := row.localDelta su
  row.nodeType = 2 ∧
    fourInterval.contains p_ ∧
    0 < ε ∧
    0 < r ∧
    RationalApprox.LocalTheorem.BoundRℚ r ε p_ (Row.QTriangle row) sl ∧
    RationalApprox.LocalTheorem.BoundDeltaℚ δ p_ (Row.PTriangle row) (Row.QTriangle row) su ∧
    (Row.PTriangle row).Aεℚ p_.vecX₁ℚ ε ∧
    (Row.QTriangle row).Aεℚ p_.vecX₂ℚ ε ∧
    (Row.PTriangle row).κSpanning p_.θ₁ p_.φ₁ ε ∧
    (Row.QTriangle row).κSpanning p_.θ₂ p_.φ₂ ε ∧
    (Row.QTriangle row).Bεℚ Nopert.poly.vertices p_ ε δ r su

def Row.localPreconditionCheck_to_precondition (row : Row)
    (su : RationalApprox.UpperSqrt) (sl : RationalApprox.LowerSqrt)
    (h : row.localPreconditionCheck su sl) :
    RationalApprox.LocalTheorem.RationalLocalTheoremPrecondition
      Nopert.poly Nopert.poly (RationalApprox.κApproxPoly.refl Nopert.poly)
      (Row.PTriangle row) (Row.QTriangle row)
      row.localPose row.localEps (row.localDelta su) (row.localR) su sl := by
  rcases h with ⟨_hnode, hp4, hε, hr, hR, hΔ, hae1, hae2, hspan1, hspan2, hbe⟩
  refine {
    hP := Row.PTriangle_mem_nopertVerts row
    hQ := Row.QTriangle_mem_nopertVerts row
    p_in_4 := hp4
    hε := hε
    hr := hr
    boundR := hR
    boundDelta := hΔ
    ae₁ := hae1
    ae₂ := hae2
    span₁ := hspan1
    span₂ := hspan2
    be := hbe
  }

end

end Solution
