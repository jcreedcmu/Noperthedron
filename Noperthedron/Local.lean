import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Lemma23

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 21 -/
theorem pythagoras {θ φ : ℝ} (P : Euc(3)) :
    ‖rotM θ φ P‖ ^ 2 = ‖P‖ ^ 2 - ⟪vecX θ φ, P⟫ ^ 2 := by
  sorry

/-- [SY25] Lemma 24 -/
theorem abs_sub_inner_bars_le {n : ℕ} (A B A_ B_ : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, B P₂⟫ - ⟪A_ P₁, B_ P₂⟫| ≤
    ‖P₁‖ * ‖P₂‖ * (‖A - A_‖ * ‖B‖ + ‖A_‖ * ‖B - B_‖ + ‖A - A_‖ * ‖A - B_‖) := by
  sorry

/-- [SY25] Lemma 25 -/
theorem abs_sub_inner_le {n : ℕ} (A B : Euc(n) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(n)) :
    |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤ ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (‖A‖ + ‖B‖ + ‖A - B‖) := by
  sorry

/-- [SY25] Lemma 26 -/
theorem origin_in_triangle {A B C : Euc(2)}
    (hA : 0 < ⟪rotR (π/2) A, B⟫) (hB : 0 < ⟪rotR (π/2) B, C⟫) (hC : 0 < ⟪rotR (π/2) C, A⟫) :
    0 ∈ interior (convexHull ℝ {A, B, C}) := by
  sorry

def Triangle : Type := Fin 3 → ℝ³

/-- The triangle P is congruent to Q in the usual geometric sense -/
def Triangle.Congruent (P Q : Triangle) : Prop := by
  sorry

/-- [SY25] Definition 27. Note that the "+ 1" at the type Fin 3 wraps. -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℝ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) < ⟪rotR (π / 2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫

/-- [SY25] Lemma 28 -/
theorem vecX_spanning {ε θ θ_ φ φ_ : ℝ} (P : Triangle)
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hSpanning: P.Spanning θ_ φ_ ε)
    (hX : ∀ i, 0 < ⟪vecX θ φ, P i⟫) :
    vecX θ φ ∈ Spanp P := by
  sorry

/-- [SY25] Lemma 30 -/
theorem inCirc {δ ε θ₁ θ₁_ θ₂ θ₂_ φ₁ φ₁_ φ₂ φ₂_ α α_: ℝ} {P Q : Euc(3)}
    (hε : 0 < ε)
    (hθ₁ : |θ₁ - θ₁_| ≤ ε) (hφ₁ : |φ₁ - φ₁_| ≤ ε)
    (hθ₂ : |θ₂ - θ₂_| ≤ ε) (hφ₂ : |φ₂ - φ₂_| ≤ ε)
    (hα : |α - α_| ≤ ε) :
    let T : Euc(2) := (1/2) • (rotR α_ (rotM θ₁_ φ₁_ P) + rotM θ₂_ φ₂_ Q)
    ‖T - rotM θ₂_ φ₂_ Q‖ ≤ δ →
    (rotR α (rotM θ₁ φ₁ P) ∈ Metric.ball T (δ + √5 * ε) ∧
     rotM θ₂ φ₂ Q ∈ Metric.ball T (δ + √5 * ε)) := by
  sorry

/-- The intersection of the δ-disc centered at Q with the interior of P -/
def sect (δ : ℝ) (Q : Euc(2)) (P : Finset Euc(2)) : Set Euc(2) := Metric.ball Q δ ∩ interior P

def LocallyMaximallyDistant (δ : ℝ) (Q Q_ : Euc(2)) (P : Finset Euc(2)) : Prop :=
  ∀ A ∈ sect δ Q_ P, ‖A‖ < ‖Q‖

theorem inner_ge_implies_LMD {P : Finset Euc(2)} {Q Q_ : Euc(2)} {δ r : ℝ}
    (hQ : Q ∈ P) (hQ_ : ‖Q - Q_‖ < δ) (hr : 0 < r) (hrQ : r < ‖Q‖)
    (hle : ∀ Pᵢ ∈ P \ {Q}, δ / r ≤ ⟪Q, Q - Pᵢ⟫ / (‖Q‖ * ‖Q - Pᵢ‖)) :
    LocallyMaximallyDistant δ Q Q_ P := by
  sorry

/-- [SY25] Lemma 33 -/
theorem coss {δ ε θ θ_ φ φ_ : ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    let M := rotM θ φ
    let M_ := rotM θ_ φ_
    (⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
     ((‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε))
    ≤
     ⟪M P, M (P - Q)⟫ / (‖M P‖ * ‖M (P - Q)‖):= by
  sorry

/--
Condition A_ε from [SY25] Theorem 36
-/
def Triangle.Aε (X : ℝ³) (P : Triangle) (ε : ℝ) : Prop :=
  ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ i : Fin 3, ⟪X, P i⟫ > ε * √2

noncomputable
def Triangle.Bε.lhs (i j : Fin 3) (Q : Triangle) (p : Pose) (ε : ℝ) : ℝ :=
   (⟪p.rotM₂ (Q i), p.rotM₂ (Q i - Q j)⟫ - 2 * ε * ‖Q i - Q j‖ * (ε + √2))
   / ((‖p.rotM₂ (Q i)‖ + ε * √2) * (‖p.rotM₂ (Q i - Q j)‖ + 2 * ε * √2))

/--
Condition B_ε from [SY25] Theorem 36
-/
def Triangle.Bε (Q : Triangle) (p : Pose) (ε δ r : ℝ) : Prop :=
  ∀ i j : Fin 3, i ≠ j →
  Triangle.Bε.lhs i j Q p ε > (δ + ε * √5) / r

instance : Membership Triangle (Finset ℝ³) where
  mem set tri := ∀ i : Fin 3, (tri i) ∈ set

/-- The condition on δ in the Local Theorem -/
def BoundDelta (δ : ℝ) (p : Pose) (P Q : Triangle) : Prop :=
  ∀ i : Fin 3, δ ≥ ‖p.rotR (p.rotM₁ (P i)) - p.rotM₂ (Q i)‖/2

/-- The condition on r in the Local Theorem -/
def BoundR (r ε : ℝ) (p : Pose) (Q : Triangle): Prop :=
  ∀ i : Fin 3, ‖p.rotM₂ (Q i)‖ > r + ε * √2

--- XXX: this is a leftover shim that should be cleaned up
noncomputable
def shape_of (S : Finset ℝ³) : Shape where
  vertices := S

-- TODO: Somehow separate out the "local theorem precondition"
-- predicate in a way that is suitable for the computational step's
-- tree check.
theorem local_theorem (P Q : Triangle)
    (cong_tri : P.Congruent Q)
    (poly : Finset ℝ³) (ne : poly.Nonempty)
    (hP : P ∈ poly) (hQ : Q ∈ poly)
    (radius_one : polyhedron_radius poly ne = 1)
    (p : Pose)
    (ε δ r : ℝ) (hε : ε > 0) (hr : r > 0)
    (hr : BoundR r ε p Q)
    (hδ : BoundDelta δ p P Q)
    (ae₁ : P.Aε p.vecX₁ ε) (ae₂ : Q.Aε p.vecX₂ ε)
    (span₁ : P.Spanning p.θ₁ p.φ₁ ε)
    (span₂ : Q.Spanning p.θ₂ p.φ₂ ε)
    (be : Q.Bε p ε δ r)
    : ∃ q ∈ p.closed_ball ε, Shadows.IsRupert q (shape_of poly |>.hull) := by
  sorry
