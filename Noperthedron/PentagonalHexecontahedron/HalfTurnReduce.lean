module

public import Noperthedron.PentagonalHexecontahedron.HalfTurn
public import Noperthedron.PentagonalHexecontahedron.AtlasHalfTurnPrune
public import Noperthedron.PentagonalHexecontahedron.IcoView

@[expose] public section

/-!
# The half-turn reduction of relative rotations

`relativeRotation_leftHalfTurn`: turning the inner copy by H_z and composing
it with G on the right changes the relative rotation R to H_u R G, where
u = `p.view` (the third row of the outer rotation) and H_u = `halfTurnMat u`.

`exists_halfTurn_ico_reduction`: among the 120 candidates R g and H_u R g
(g ∈ I) one of maximal trace lies both in the icosahedral cell and in the
half-turn cell (`InHalfTurnCell`), since H_u² = 1 and I is a group.
-/

namespace Noperthedron.PentagonalHexecontahedron

open scoped Matrix

theorem view_sq_sum (p : MatrixPose) : ∑ k, p.view k ^ 2 = 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp p.outerRot.property.1
  have h22 := congrFun (congrFun h 2) 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h22
  simpa [MatrixPose.view, sq] using h22

theorem halfTurnMat_view (p : MatrixPose) :
    halfTurnMat p.view = p.outerRot.valᵀ * halfTurnZMat * p.outerRot.val := by
  have horth := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp p.outerRot.property.1
  have hs : p.outerRot.val 2 0 ^ 2 + p.outerRot.val 2 1 ^ 2 + p.outerRot.val 2 2 ^ 2 = 1 := by
    have := view_sq_sum p
    simpa [MatrixPose.view, Fin.sum_univ_three] using this
  ext i j
  have hij := congrFun (congrFun horth i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at hij
  simp only [halfTurnMat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, halfTurnZMat,
    MatrixPose.view, hs, div_one]
  simp [Matrix.of_apply, Matrix.one_apply] at hij ⊢
  split_ifs at hij ⊢ <;> linarith

theorem relativeRotation_leftHalfTurn (p : MatrixPose) (G : SO3) :
    (p.leftHalfTurn G).relativeRotation = halfTurnMat p.view * p.relativeRotation * G.val := by
  have horth := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp p.outerRot.property.1
  rw [halfTurnMat_view]
  simp only [MatrixPose.relativeRotation, MatrixPose.leftHalfTurn, halfTurnZ]
  show p.outerRot.valᵀ * (halfTurnZMat * p.innerRot.val * G.val) = _
  rw [show p.outerRot.valᵀ * halfTurnZMat * p.outerRot.val * (p.outerRot.valᵀ * p.innerRot.val) * G.val =
      p.outerRot.valᵀ * halfTurnZMat * (p.outerRot.val * p.outerRot.valᵀ) * p.innerRot.val * G.val by
    simp only [Matrix.mul_assoc]]
  rw [horth, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem halfTurnMat_mul_self (u : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 ≠ 0) :
    halfTurnMat u * halfTurnMat u = 1 := by
  ext i j
  simp only [halfTurnMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at hu ⊢
  field_simp
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> nlinarith [hu]

/-- The candidate (b, g): (H_u if b) · R · g. -/
noncomputable def htCandidate (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (b : Bool) (g : IcoIndex) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (if b then halfTurnMat u else 1) * R * icoMatrix g

theorem exists_halfTurn_ico_reduction (u : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 ≠ 0)
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ b g, InIcoFundamentalDomain (htCandidate u R b g) ∧ InHalfTurnCell u (htCandidate u R b g) := by
  obtain ⟨⟨b, g⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun bg : Bool × IcoIndex => Matrix.trace (htCandidate u R bg.1 bg.2)) Finset.univ_nonempty
  refine ⟨b, g, fun g' => ?_, fun g' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_icoMatrix_mul g g'
    have := hmax (b, k) (Finset.mem_univ _)
    simp only [htCandidate] at this ⊢
    rw [Matrix.mul_assoc _ (icoMatrix g), hk]
    exact this
  · obtain ⟨k, hk⟩ := exists_icoMatrix_mul g g'
    have := hmax (!b, k) (Finset.mem_univ _)
    have hH := halfTurnMat_mul_self u hu
    have heq : halfTurnMat u * htCandidate u R b g * icoMatrix g' = htCandidate u R (!b) k := by
      cases b
      · simp only [htCandidate, Bool.false_eq_true, if_false, Bool.not_false, if_true, Matrix.one_mul]
        simp only [Matrix.mul_assoc, hk]
      · simp only [htCandidate, if_true, Bool.not_true, Bool.false_eq_true, if_false, Matrix.one_mul]
        calc halfTurnMat u * (halfTurnMat u * R * icoMatrix g) * icoMatrix g'
            = (halfTurnMat u * halfTurnMat u) * R * (icoMatrix g * icoMatrix g') := by
              simp only [Matrix.mul_assoc]
          _ = R * icoMatrix k := by rw [hH, hk, Matrix.one_mul]
    rw [heq]
    exact this

end Noperthedron.PentagonalHexecontahedron
