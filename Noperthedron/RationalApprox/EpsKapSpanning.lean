import Noperthedron.Basic
import Noperthedron.RationalApprox.Basic
import Noperthedron.Local.EpsSpanning
import Noperthedron.RationalApprox.Lemma42

namespace RationalApprox

open scoped RealInnerProductSpace Real
open scoped Matrix


/-- [SY25] Definition 45. Note that the "+ 1" at the type Fin 3 wraps.
  We don't include in this definition the constraint that θ, φ ∈ [-4, 4] or
  that ‖P₁‖, ‖P₂‖, ‖P₃‖ ≤ 1 + κ.
  If a user of this code wants to impose those, they'll have to separately. -/
/- QUESTION: should be we be casting to ℝ to take the inner product?;
   on the one hand, we don't *have* to, because rotR (π / 2) is a valid 90° rotation on rationals.
   And should ε be real or rational? -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℝ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) + 6 * κ <
      ⟪rotR (π / 2) (rotMℚ θ φ (P i)), rotMℚ θ φ (P (i + 1))⟫

def κApproxTri (A : Local.Triangle) (A' : RationalApprox.Triangle) : Prop :=
  ∀ i, ‖A i - (↑(A' i) : ℝ³)‖ ≤ κ

/- [SY25 Lemma 46] -/
theorem ek_spanning_imp_e_spanning (P : Local.Triangle) (P' : RationalApprox.Triangle)
    (hk : κApproxTri P P') (θ φ ε : ℝ) (hspan : P'.Spanning θ φ ε) : P.Spanning θ φ ε := by
  constructor
  · exact hspan.pos
  · have lt := hspan.lt
    intro i
    suffices h : |⟪(rotR (π / 2)) (rotM θ φ (P i)),  rotM θ φ (P (i + 1))⟫
                 - ⟪(rotR (π / 2)) (rotMℚ θ φ (P' i)), rotMℚ θ φ (P' (i + 1))⟫| ≤ 6 * κ by
      calc ⟪(rotR (π / 2)) ((rotM θ φ) (P i)), (rotM θ φ) (P (i + 1))⟫
      _ ≥ ⟪(rotR (π / 2)) (rotMℚ θ φ (P' i)), rotMℚ θ φ (P' (i + 1))⟫ - 6 * κ :=
        sub_le_of_abs_sub_le_left h
      _ > 2 * ε * (√2 + ε) := lt_tsub_of_add_lt_right (hspan.lt i)

    let mv : MatVec 1 1 := sorry -- (A) P (i + 1)ᵀ ∘ (rotM θ φ)ᵀ ∘ rotR (π / 2) ∘ rotM θ φ ∘ P i
                                 -- (B) P' (i + 1)ᵀ ∘ (rotMℚ θ φ)ᵀ ∘ rotR (π / 2) ∘ rotMℚ θ φ ∘ P' i
    have hmvs : mv.size = 5 := by sorry
    have hnlp : mv.maxNormList.prod = (1 + κ)^4 := by sorry
    have hva : ⟪(rotR (π / 2)) ((rotM θ φ) (P i)), (rotM θ φ) (P (i + 1))⟫ = mv.valA := by sorry
    have hvb : ⟪(rotR (π / 2)) (rotMℚ θ φ (P' i)), rotMℚ θ φ (P' (i + 1))⟫ = mv.valB := by sorry
    have hdbb : mv.DiffBoundedBy κ := by sorry
    suffices h : |mv.valA - mv.valB| ≤ 6 * κ by simpa [hva, hvb] using h
    grw [norm_sub_le_prod1 mv κ (by norm_num [κ]) hdbb]
    rw [hmvs, hnlp]
    norm_num [κ]
