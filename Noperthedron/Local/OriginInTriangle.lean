import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.PoseInterval
import Noperthedron.Local.Prelims

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 26 -/
theorem origin_in_triangle {A B C : Euc(2)}
    (hA : 0 < ⟪rotR (π/2) A, B⟫) (hB : 0 < ⟪rotR (π/2) B, C⟫) (hC : 0 < ⟪rotR (π/2) C, A⟫) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a • A + b • B + c • C = 0 := by
  refine ⟨⟪rotR (π/2) B, C⟫, ⟪rotR (π/2) C, A⟫, ⟪rotR (π/2) A, B⟫, hB, hC, hA, ?_⟩
  (ext i; fin_cases i) <;>
    simp [rotR, rotR_mat, EuclideanSpace.inner_eq_star_dotProduct, Matrix.vecHead,
      Matrix.vecTail] <;>
    ring_nf
